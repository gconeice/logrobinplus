#include <random>
#include "robin_utils.h"
#include "emp-zk/emp-zk.h"
#include <iostream>
#include "emp-tool/emp-tool.h"
#if defined(__linux__)
	#include <sys/time.h>
	#include <sys/resource.h>
#elif defined(__APPLE__)
	#include <unistd.h>
	#include <sys/resource.h>
	#include <mach/mach.h>
#endif

using namespace emp;
using namespace std;

int port, party;
const int threads = 1;

uint64_t comm(BoolIO<NetIO> *ios[threads]) {
	uint64_t c = 0;
	for(int i = 0; i < threads; ++i)
		c += ios[i]->counter;
	return c;
}
uint64_t comm2(BoolIO<NetIO> *ios[threads]) {
	uint64_t c = 0;
	for(int i = 0; i < threads; ++i)
		c += ios[i]->io->counter;
	return c;
}

void test_circuit_zk(BoolIO<NetIO> *ios[threads], int party, size_t branch_size, size_t nin, size_t nx) {

    // size_t log_branch_size = branch_size;
    branch_size = 1 << branch_size;

    // initial zk exec
    auto init_start = clock_start();
    auto init_time = time_from(init_start);    
    setup_zk_arith<BoolIO<NetIO>>(ios, threads, party);

    // obtain delta
    uint64_t delta = LOW64(ZKFpExec::zk_exec->get_delta());
	std::cout << "DELTA = " << delta << std::endl;    

    // set up randomized disjunctive circuits
    std::random_device::result_type cir_seed;
    if (party == ALICE) {
        std::random_device rd; // obtain a random number from hardware
        cir_seed = rd();
        ZKFpExec::zk_exec->send_data(&cir_seed, sizeof(std::random_device::result_type));
    } else {
        ZKFpExec::zk_exec->recv_data(&cir_seed, sizeof(std::random_device::result_type));
    }
    auto cir_gen = std::mt19937(cir_seed);

    // generate random circuits for disjunctive statement
    std::vector<Circuit> cir;
    for (size_t bid = 0; bid < 1; bid++) {
        cir.push_back(Circuit(nin, nx));
        cir[cir.size()-1].rand_cir(cir_gen);
    }

    // for P to generate a random active index
    size_t id = 0;
    if (party == ALICE) {
        std::random_device rd; // obtain a random number from hardware
        auto id_seed = rd();
        auto id_gen = std::mt19937(id_seed);        
        std::uniform_int_distribution<> distr(0, 1-1);
        id = distr(id_gen);
    }

    // for P to generate a random witness
    f61 final_res;
    std::vector<f61> win, wl, wr, wo;

    // test for a single circuit now
    if (party == ALICE) {
        std::random_device rd; // obtain a random number from hardware
        auto wit_seed = rd();
        auto wit_gen = std::mt19937(wit_seed);
        final_res = cir[id].f61_gen_wit(wit_gen, win, wl, wr, wo);
        ZKFpExec::zk_exec->send_data(&final_res, sizeof(f61));
    } else {
        ZKFpExec::zk_exec->recv_data(&final_res, sizeof(f61));
    }

    // testing communication
    uint64_t com1 = comm(ios);
	uint64_t com11 = comm2(ios);
    auto start = clock_start();

    // Alice commit the input
    std::vector<IntFp> com_in;
    for (size_t i = 0; i < nin; i++) com_in.push_back( IntFp(party == ALICE ? win[i].val : 0, ALICE) );

    // Alice commit the l and r
    std::vector<IntFp> com_l, com_r, com_o;
    for (size_t i = 0; i < nx; i++) com_l.push_back( IntFp(party == ALICE ? wl[i].val : 0, ALICE) );
    for (size_t i = 0; i < nx; i++) com_r.push_back( IntFp(party == ALICE ? wr[i].val : 0, ALICE) );

    // Alice and Bob generate o
    for (size_t i = 0; i < nx; i++) com_o.push_back( com_l[i] * com_r[i] );

    // Bob issues random challenges via PRG over a seed
    block alpha_seed; 
    if (party == ALICE) {
		ZKFpExec::zk_exec->recv_data(&alpha_seed, sizeof(block));
    } else {
        PRG().random_block(&alpha_seed, 1);
        ZKFpExec::zk_exec->send_data(&alpha_seed, sizeof(block));
    }
    PRG prg_alpha(&alpha_seed);
    std::vector<f61> alpha_power;
    for (size_t i = 0; i < 2*nx+1; i++) {
        block tmptmp;
        prg_alpha.random_block(&tmptmp, 1);
		uint64_t coeff = LOW64(tmptmp) % PR; 
        alpha_power.push_back( f61(coeff) );
    }

    // Go over every single branch
    std::vector<IntFp> bmac;
    for (size_t bid = 0; bid < branch_size; bid++) bmac.push_back( cir[0].robin_acc(com_in, com_l, com_r, com_o, alpha_power, PR - final_res.val) );

    // prove that the product is 0
    IntFp final_prod = IntFp(1, PUBLIC);
    for (size_t bid = 0; bid < branch_size; bid++) final_prod = final_prod * bmac[bid];
    batch_reveal_check_zero(&final_prod, 1);

	finalize_zk_arith<BoolIO<NetIO>>();
	auto timeuse = time_from(start);	
	cout << init_time+timeuse << " us\t" << party << " " << endl;
	std::cout << std::endl;

	uint64_t com2 = comm(ios) - com1;
	uint64_t com22 = comm2(ios) - com11;
	std::cout << "communication (B): " << com2 << std::endl;
	std::cout << "communication (B): " << com22 << std::endl;

#if defined(__linux__)
	struct rusage rusage;
	if (!getrusage(RUSAGE_SELF, &rusage))
		std::cout << "[Linux]Peak resident set size: " << (size_t)rusage.ru_maxrss << std::endl;
	else std::cout << "[Linux]Query RSS failed" << std::endl;
#elif defined(__APPLE__)
	struct mach_task_basic_info info;
	mach_msg_type_number_t count = MACH_TASK_BASIC_INFO_COUNT;
	if (task_info(mach_task_self(), MACH_TASK_BASIC_INFO, (task_info_t)&info, &count) == KERN_SUCCESS)
		std::cout << "[Mac]Peak resident set size: " << (size_t)info.resident_size_max << std::endl;
	else std::cout << "[Mac]Query RSS failed" << std::endl;
#endif
}

int main(int argc, char** argv) {

	size_t branch_size = 0;
	size_t nin = 0;
    size_t nx = 0;
	if(argc < 7) {
		std::cout << "usage: exe PARTY PORT IP LOG_BRANCH_SIZE CIR_IN_SIZE CIR_MULT_SIZE" << std::endl;
		return -1;
	} else {
        branch_size = atoi(argv[4]);
        nin = atoi(argv[5]);
        nx = atoi(argv[6]);
	}

	parse_party_and_port(argv, &party, &port);
	BoolIO<NetIO>* ios[threads];
	for(int i = 0; i < threads; ++i)
		ios[i] = new BoolIO<NetIO>(new NetIO(party == ALICE?nullptr:argv[3],port+i), party==ALICE);

	std::cout << std::endl << "------------ circuit zero-knowledge proof test ------------" << std::endl << std::endl;;


	
	test_circuit_zk(ios, party, branch_size, nin, nx);

	for(int i = 0; i < threads; ++i) {
		delete ios[i]->io;
		delete ios[i];
	}
	return 0;

}