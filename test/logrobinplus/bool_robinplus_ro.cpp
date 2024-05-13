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
    setup_zk_bool<BoolIO<NetIO>>(ios, threads, party);

    // set up randomized disjunctive circuits
    std::random_device::result_type cir_seed;
    if (party == ALICE) {
        std::random_device rd; // obtain a random number from hardware
        cir_seed = rd();
        ios[0]->send_data(&cir_seed, sizeof(std::random_device::result_type));
        ios[0]->flush();
    } else {
        ios[0]->recv_data(&cir_seed, sizeof(std::random_device::result_type));
    }
    auto cir_gen = std::mt19937(cir_seed);

    // generate random circuits for disjunctive statement
    std::vector<Circuit> cir;
    for (size_t bid = 0; bid < branch_size; bid++) {
        cir.push_back(Circuit(nin, nx));
        cir[cir.size()-1].rand_cir(cir_gen);
    }

    // for P to generate a random active index
    size_t id = 0;
    if (party == ALICE) {
        std::random_device rd; // obtain a random number from hardware
        auto id_seed = rd();
        auto id_gen = std::mt19937(id_seed);        
        std::uniform_int_distribution<> distr(0, branch_size-1);
        id = distr(id_gen);
    }

    // for P to generate a random witness
    f2 final_res;
    std::vector<f2> win, wl, wr, wo;

    // test for a single circuit now
    if (party == ALICE) {
        std::random_device rd; // obtain a random number from hardware
        auto wit_seed = rd();
        auto wit_gen = std::mt19937(wit_seed);
        final_res = cir[id].f2_gen_wit(wit_gen, win, wl, wr, wo);
        ios[0]->send_data(&final_res, sizeof(f2));
        ios[0]->flush();
    } else {
        ios[0]->recv_data(&final_res, sizeof(f2));
    }

    block delta = get_bool_delta<BoolIO<NetIO>>(party);

    // testing communication
    uint64_t com1 = comm(ios);
	uint64_t com11 = comm2(ios);
    auto start = clock_start();

    // Alice commit the input
    std::vector<Bit> com_in;
    for (size_t i = 0; i < nin; i++) com_in.push_back( Bit(party == ALICE ? win[i].val : 0, ALICE) );

    // Alice commit the o
    std::vector<Bit> com_o;
    for (size_t i = 0; i < nx; i++) com_o.push_back( Bit(party == ALICE ? wo[i].val : 0, ALICE) );

    // Bob issues random challenges via PRG over a seed
    block alpha_seed; 
    if (party == ALICE) {
		ios[0]->recv_data(&alpha_seed, sizeof(block));
    } else {
        PRG().random_block(&alpha_seed, 1);
        ios[0]->send_data(&alpha_seed, sizeof(block));
        ios[0]->flush();
    }
    PRG prg_alpha(&alpha_seed);
    std::vector<gf128bit> alpha_power;
    for (size_t i = 0; i < nx+1; i++) {
        block tmptmp;
        prg_alpha.random_block(&tmptmp, 1);
        alpha_power.push_back( gf128bit(tmptmp) );
    }    

    // Go over every single branch
    std::vector<gf128bitTriple> M; // hold by P
    std::vector<gf128bit> K; // hold by V
    if (party == ALICE) {
        for (size_t bid = 0; bid < branch_size; bid++) M.push_back( cir[bid].robinplus_acc_P(com_in, com_o, alpha_power, final_res) );
        assert( M[id].coef[2] == gf128bit::zero() );
    } else {
        for (size_t bid = 0; bid < branch_size; bid++) K.push_back( cir[bid].robinplus_acc_V(com_in, com_o, alpha_power, final_res, gf128bit(delta)) );
    }

    // testing codes
    // if (party == BOB) {
    //     ios[0]->send_data(&delta, sizeof(block));
    //     ios[0]->flush();
    // } else {
    //     ios[0]->recv_data(&delta, sizeof(block));
    // }

    // if (party == ALICE) {
    //     for (size_t bid = 0; bid < branch_size; bid++) {
    //         cout << bid << ": " << (M[bid].coef[2] * gf128bit(delta) * gf128bit(delta) + M[bid].coef[1] * gf128bit(delta) + M[bid].coef[0]).val << endl;
    //     }            
    // } else {
    //     for (size_t bid = 0; bid < branch_size; bid++) {
    //         cout << bid << ": " << K[bid].val << endl;
    //     }
    // }

    // Ask P to commit the quardratic term
    std::vector<ext_f2> com_Q;
    for (size_t bid = 0; bid < branch_size; bid++) {
        ext_f2 tmp = ext_f2::uniform();
        if (party == ALICE) {
            gf128bit diff = tmp.val + M[bid].coef[2];
            ios[0]->send_data(&diff, sizeof(gf128bit));
            ios[0]->flush();
            tmp.val = M[bid].coef[2];
        } else {
            gf128bit diff;
            ios[0]->recv_data(&diff, sizeof(gf128bit));
            tmp.key += diff * delta;
        }
        com_Q.push_back(tmp);
    }

    // P proves that the product is 0
    prove_product_zero_ro(ios, party, com_Q);

    // V (Bob) issues random challenge to randomly combine quadratic equation
    // Bob issues random challanges alpha and parties compute its powers
    block beta_seed; 
    if (party == ALICE) {
		ios[0]->recv_data(&beta_seed, sizeof(block));
    } else {
        PRG().random_block(&beta_seed, 1);
        ios[0]->send_data(&beta_seed, sizeof(block));
        ios[0]->flush();
    }
    PRG prg_beta(&beta_seed);
    gf128bitTriple acc_M;
    gf128bit acc_K;
    gf128bit beta_coeff;
    ext_f2 acc_Q;

    if (party == ALICE) {
        for (size_t i = 0; i < branch_size; i++) {
            prg_beta.random_block(&beta_coeff.val, 1);
            acc_Q.val += beta_coeff * com_Q[i].val;
            acc_Q.key += beta_coeff * com_Q[i].key;
            acc_M.coef[1] += beta_coeff * M[i].coef[1];
            acc_M.coef[0] += beta_coeff * M[i].coef[0];
        }
    } else {
        for (size_t i = 0; i < branch_size; i++) {
            prg_beta.random_block(&beta_coeff.val, 1);
            acc_Q.key += beta_coeff * com_Q[i].key;
            acc_K += beta_coeff * K[i];
        }
    }    
    // randomized to add ZK
    //std::vector<IntFp> bdelta;
    ext_f2 r2, r1;
    r2 = ext_f2::uniform();
    r1 = ext_f2::uniform();
    acc_Q.val += r2.val;
    acc_Q.key += r2.key;
    if (party == ALICE) {
        acc_M.coef[1] += r2.key + r1.val;
        acc_M.coef[0] += r1.key;
        ios[0]->send_data(&acc_M, sizeof(gf128bitTriple));
        ios[0]->flush();
    } else {
        acc_K += r2.key * gf128bit(delta) + r1.key;
        ios[0]->recv_data(&acc_M, sizeof(gf128bitTriple));
    }

    // P opens acc_Q to V
    if (party == ALICE) {
        ios[0]->send_data(&acc_Q.val, sizeof(gf128bit));
        ios[0]->send_data(&acc_Q.key, sizeof(gf128bit));
        ios[0]->flush();
    } else {
        gf128bit value, mac;
        ios[0]->recv_data(&value, sizeof(gf128bit));
        ios[0]->recv_data(&mac, sizeof(gf128bit));
        //cout << (value * gf128bit(delta) + mac).val << " = " << acc_Q.key.val << endl;
        assert( value * gf128bit(delta) + mac == acc_Q.key );
        acc_M.coef[2] = value;
    }

    // checking the quardratic equality
    if (party == BOB) {
        // cout << (gf128bit(delta) * gf128bit(delta) * acc_M.coef[2] + gf128bit(delta) * acc_M.coef[1] + acc_M.coef[0]).val << ' ' << acc_K.val << std::endl;
        assert( gf128bit(delta) * gf128bit(delta) * acc_M.coef[2] + gf128bit(delta) * acc_M.coef[1] + acc_M.coef[0] == acc_K );
    }    
    
	finalize_zk_bool<BoolIO<NetIO>>();
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