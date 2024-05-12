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

    size_t log_branch_size = branch_size;
    branch_size = 1 << branch_size;

    // testing communication
    uint64_t com1 = comm(ios);
	uint64_t com11 = comm2(ios);

    // initial zk exec
    auto init_start = clock_start();
    setup_zk_arith<BoolIO<NetIO>>(ios, threads, party);
    auto init_time = time_from(init_start);

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

    auto start = clock_start();

    // Alice commit the input
    std::vector<IntFp> com_in;
    for (size_t i = 0; i < nin; i++) com_in.push_back( IntFp(party == ALICE ? win[i].val : 0, ALICE) );

    // Alice commit the o
    std::vector<IntFp> com_o;
    for (size_t i = 0; i < nx; i++) com_o.push_back( IntFp(party == ALICE ? wo[i].val : 0, ALICE) );

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
    for (size_t i = 0; i < nx+1; i++) {
        block tmptmp;
        prg_alpha.random_block(&tmptmp, 1);
		uint64_t coeff = LOW64(tmptmp) % PR; 
        alpha_power.push_back( f61(coeff) );
    }

    // Go over every single branch
    std::vector<f61Triple> M; // hold by P
    std::vector<f61> K; // hold by V
    if (party == ALICE) {
        for (size_t bid = 0; bid < branch_size; bid++) M.push_back( cir[0].robinplus_acc_P(com_in, com_o, alpha_power, PR - final_res.val) );
        assert( M[id].coef[2].val == 0 );
    } else {
        for (size_t bid = 0; bid < branch_size; bid++) K.push_back( cir[0].robinplus_acc_V(com_in, com_o, alpha_power, PR - final_res.val, f61(delta)) );
    }

    // Alice commits to id_i for each decomposied bit
    std::vector<IntFp> com_id;
    for (size_t tmp_id = id, i = 0; i < log_branch_size; i++, tmp_id >>= 1) com_id.push_back( IntFp(tmp_id%2, ALICE) );

    // Alice proves to Bob that the committed values is {0,1}^*
    prove01vector_ro(party, com_id, f61(delta));

    // Alice and Bob prepare [\delta]
    std::vector<IntFp> bdelta;
    for (size_t i = 0; i < log_branch_size; i++) {
        IntFp tmp;
        tmp.value = ZKFpExec::zk_exec->get_one_role();
        bdelta.push_back( tmp );
    }

    // Alice and Bob prepare the randomized masks
    IntFp r[log_branch_size+1][2];
    r[log_branch_size][0].value = ZKFpExec::zk_exec->get_one_role();
    for (size_t i = 0; i < log_branch_size; i++) {
        r[i][0].value = ZKFpExec::zk_exec->get_one_role();
        r[i][1].value = ZKFpExec::zk_exec->get_one_role();
    }

    // Alice prepares the coefficients for the final polynomial
    std::vector<IntFp> poly_coeff;
    f61 row2[log_branch_size];
    f61 row1[log_branch_size+1];
    if (party == ALICE) {    
        std::vector<std::vector<f61>> final_acc; final_acc.resize(log_branch_size+1, vector<f61>(3));            
        std::vector<f61> tmp_acc; tmp_acc.push_back( f61::unit() );
        for (size_t i = 0; i < log_branch_size; i++) tmp_acc.push_back( f61::zero() );
        compPcoeff(0, id, 0, bdelta, M, final_acc, tmp_acc);
        //cout << final_acc[log_branch_size][2].val << endl;
        assert(final_acc[log_branch_size][2].val == 0);

        // Alice add the randomization
        // for the log_branch_size one
        final_acc[log_branch_size][1] += f61::minor( HIGH64(r[log_branch_size][0].value) );
        final_acc[log_branch_size][0] += f61( LOW64(r[log_branch_size][0].value) );
        for (size_t i = 0; i < log_branch_size; i++) {
            final_acc[i][2] += f61::minor( HIGH64(r[i][1].value) );
            final_acc[i][1] += f61::minor( HIGH64(r[i][0].value) ) + f61( LOW64(r[i][1].value) );
            final_acc[i][0] += f61( LOW64(r[i][0].value) );
        }

        // Alice commits to the constant terms
        for (size_t i = 0; i < log_branch_size+1; i++) poly_coeff.push_back( IntFp(final_acc[i][0].val, ALICE) );

        // Alice sends randomized coefficients on other terms
        for (size_t i = 0; i < log_branch_size; i++) {
            row2[i] = final_acc[i][2];
            row1[i] = final_acc[i][1];
        }
        row1[log_branch_size] = final_acc[log_branch_size][1];
        ZKFpExec::zk_exec->send_data(&row2, sizeof(f61) * log_branch_size);
        ZKFpExec::zk_exec->send_data(&row1, sizeof(f61) * (log_branch_size+1));      
    } else {
        // Alice commits to the constant terms
        for (size_t i = 0; i < log_branch_size+1; i++) poly_coeff.push_back( IntFp(0, ALICE) );
        // Alice sends randomized coefficients on other terms
        ZKFpExec::zk_exec->recv_data(&row2, sizeof(f61) * log_branch_size);
        ZKFpExec::zk_exec->recv_data(&row1, sizeof(f61) * (log_branch_size+1));        
    }    

    // Bob issues \Lambda to evaluate the polynomial
    f61 Lambda;
    if (party == ALICE) {
        uint64_t tmp;
		ZKFpExec::zk_exec->recv_data(&tmp, sizeof(uint64_t));
        tmp = tmp % PR; // to prevent cheating V
        Lambda = f61(tmp);
    } else {
        uint64_t tmp;
		PRG().random_data(&tmp, sizeof(uint64_t));
		tmp = tmp % PR;
		ZKFpExec::zk_exec->send_data(&tmp, sizeof(uint64_t));	        
        Lambda = f61(tmp);
    }    

    // Alice opens the second row of the path mat
    std::vector<f61> pathmat_row;
    for (size_t i = 0; i < log_branch_size; i++) {
        IntFp tmp = com_id[i] * Lambda.val + bdelta[i];
        pathmat_row.push_back( f61( tmp.reveal() ) );
    }

    // Bob expands the pathmat
    if (party == ALICE) {
        
        // ALICE prepares the last row
        IntFp acc_poly_coeff(0, PUBLIC);
        f61 coeff_Lambda = f61::unit();
        for (size_t i = 0; i <= log_branch_size; i++) {
            acc_poly_coeff = acc_poly_coeff + (poly_coeff[i] * coeff_Lambda.val);
            coeff_Lambda *= Lambda;
        }
        acc_poly_coeff.reveal();

    } else {
        std::vector<f61> expand_vec(branch_size);
        expand_pathmat(0, 0, f61::unit(), pathmat_row, expand_vec, Lambda);    
        // Bob/V computes the polynomial evaluation using K with two ways
        f61 acc_K, acc_K_2;
        f61 f61_delta(delta); f61 f61_delta_2 = f61_delta * f61_delta;
        IntFp acc_poly_coeff(0, PUBLIC);        
        for (size_t i = 0; i < branch_size; i++) acc_K += expand_vec[i] * K[i];
        // Bob add the randomization into acc_K
        f61 coeff_Lambda = f61::unit();
        for (size_t i = 0; i < log_branch_size; i++) {
            acc_K += coeff_Lambda * f61_delta * f61( LOW64(r[i][1].value) ) + coeff_Lambda * f61( LOW64(r[i][0].value) );
            acc_poly_coeff = acc_poly_coeff + (poly_coeff[i] * coeff_Lambda.val);
            acc_K_2 += row1[i] * coeff_Lambda * f61_delta;
            acc_K_2 += row2[i] * coeff_Lambda * f61_delta_2;
            coeff_Lambda *= Lambda;
        }
        acc_K += coeff_Lambda * f61( LOW64(r[log_branch_size][0].value) );
        acc_K_2 += row1[log_branch_size] * coeff_Lambda * f61_delta;
        acc_poly_coeff = acc_poly_coeff + (poly_coeff[log_branch_size] * coeff_Lambda.val);
        acc_K_2 += f61( acc_poly_coeff.reveal() );

        //std::cout << acc_K.val << ' ' << acc_K_2.val << std::endl;
        assert(acc_K.val == acc_K_2.val);
    }

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