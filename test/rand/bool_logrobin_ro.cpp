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

    // Alice commit the l and r
    std::vector<Bit> com_l, com_r, com_o;
    for (size_t i = 0; i < nx; i++) com_l.push_back( Bit(party == ALICE ? wl[i].val : 0, ALICE) );
    for (size_t i = 0; i < nx; i++) com_r.push_back( Bit(party == ALICE ? wr[i].val : 0, ALICE) );

    // Alice and Bob generate o
    for (size_t i = 0; i < nx; i++) com_o.push_back( com_l[i] & com_r[i] );

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
    for (size_t i = 0; i < 2*nx+1; i++) {
        block tmptmp;
        prg_alpha.random_block(&tmptmp, 1);
        alpha_power.push_back( gf128bit(tmptmp) );
    }    

    // Go over every single branch
    std::vector<ext_f2> bmac;
    for (size_t bid = 0; bid < branch_size; bid++) bmac.push_back( cir[bid].robin_acc(com_in, com_l, com_r, com_o, alpha_power, final_res) );

    // for (size_t bid = 0; bid < branch_size; bid++) cout << bid << ": " << bmac[bid].val.val << std::endl;
    // testing codes
    // if (party == BOB) {
    //     ios[0]->send_data(&delta, sizeof(block));
    //     ios[0]->flush();
    // } else {
    //     ios[0]->recv_data(&delta, sizeof(block));
    // }

    // if (party == ALICE) {
    //     for (size_t bid = 0; bid < branch_size; bid++) {
    //         cout << bid << ": " << (bmac[bid].val * gf128bit(delta) + bmac[bid].key).val << endl;
    //     }            
    // } else {
    //     for (size_t bid = 0; bid < branch_size; bid++) {
    //         cout << bid << ": " << bmac[bid].key.val << endl;
    //     }
    // }

    // prove that bmac[id] is 0

    // Alice commits to id_i for each decomposied bit
    std::vector<Bit> com_id;
    for (size_t tmp_id = id, i = 0; i < log_branch_size; i++, tmp_id >>= 1) com_id.push_back( Bit(tmp_id%2, ALICE) );

    // Alice proves to Bob that the committed values is {0,1}^*
    // prove01vector_it(ios, party, com_id, gf128bit(delta));
    // This step is not needed for boolean case since Alice always commits to a bit
    // COOOOOOOL!

    // Alice and Bob prepare [\delta]
    std::vector<ext_f2> bdelta(log_branch_size);
    for (size_t i = 0; i < log_branch_size; i++) bdelta[i] = ext_f2::uniform();

    // Alice prepares the coefficients for the final polynomial
    std::vector<ext_f2> poly_coeff;
    if (party == ALICE) {
        std::vector<gf128bit> final_acc; 
        for (size_t i = 0; i < log_branch_size+1; i++) final_acc.push_back( gf128bit::zero() );
        std::vector<gf128bit> tmp_acc; tmp_acc.push_back( gf128bit::unit() );
        for (size_t i = 0; i < log_branch_size; i++) tmp_acc.push_back( gf128bit::zero() );
        compPcoeff(0, id, 0, bdelta, bmac, final_acc, tmp_acc);
        //cout << final_acc[log_branch_size].val << endl;
        assert(final_acc[log_branch_size] == gf128bit::zero());
        for (size_t i = 0; i < log_branch_size; i++) {
            ext_f2 tmp = ext_f2::uniform();
            gf128bit diff = tmp.val + final_acc[i];
            tmp.val = final_acc[i];
            ios[0]->send_data(&diff, sizeof(gf128bit));
            poly_coeff.push_back( tmp );
        }
        ios[0]->flush();
    } else {
        for (size_t i = 0; i < log_branch_size; i++) {
            ext_f2 tmp = ext_f2::uniform();
            gf128bit diff;
            ios[0]->recv_data(&diff, sizeof(gf128bit));
            tmp.key += gf128bit(delta) * diff;
            poly_coeff.push_back( tmp );
        }
    }    

    // Bob issues \Lambda to evaluate the polynomial
    gf128bit Lambda;
    if (party == ALICE) {
        ios[0]->recv_data(&Lambda, sizeof(gf128bit));
    } else {
		PRG().random_data(&Lambda, sizeof(gf128bit));
        ios[0]->send_data(&Lambda, sizeof(gf128bit));
        ios[0]->flush();
    }    

    // Alice opens the second row of the path mat
    gf128bit pathmat_row[log_branch_size];
    gf128bit pathmat_row_mac[log_branch_size];
    if (party == ALICE) {
        for (size_t i = 0; i < log_branch_size; i++) {
            pathmat_row[i] = bdelta[i].val;
            pathmat_row_mac[i] = bdelta[i].key;
            if (getLSB(com_id[i].bit)) {
                pathmat_row[i] += Lambda;                
            }
            pathmat_row_mac[i] += Lambda * gf128bit( com_id[i].bit );
        }
        ios[0]->send_data(&pathmat_row, sizeof(gf128bit)*log_branch_size);
        ios[0]->send_data(&pathmat_row_mac, sizeof(gf128bit)*log_branch_size);
        ios[0]->flush();
    } else {
        ios[0]->recv_data(&pathmat_row, sizeof(gf128bit)*log_branch_size);
        ios[0]->recv_data(&pathmat_row_mac, sizeof(gf128bit)*log_branch_size);
        // Bob check if each openining is correctly
        for (size_t i = 0; i < log_branch_size; i++) {
            gf128bit check_key = Lambda * gf128bit( com_id[i].bit ) + bdelta[i].key;
            //std::cout << i << ": " << check_key.val << ' ' << (pathmat_row[i] * gf128bit(delta) + pathmat_row_mac[i]).val << endl;
            assert( check_key == pathmat_row[i] * gf128bit(delta) + pathmat_row_mac[i] );
        }
    }

    std::vector<gf128bit> row;
    for (size_t i = 0; i < log_branch_size; i++) row.push_back( pathmat_row[i] );
    // Both parties expand the pathmat
    std::vector<gf128bit> expand_vec(branch_size);
    expand_pathmat(0, 0, gf128bit::unit(), row, expand_vec, Lambda);

    // accumulate using two ways
    Bit zero(false, PUBLIC);
    gf128bit acc1; acc1 = gf128bit( zero.bit );
    gf128bit acc2; acc2 = gf128bit( zero.bit );
    for (size_t i = 0; i < branch_size; i++) {
        acc1 += bmac[i].key * expand_vec[i];
    }
    gf128bit Lambda_pow = gf128bit::unit();
    for (size_t i = 0; i < log_branch_size; i++) {
        acc2 = acc2 + poly_coeff[i].key * Lambda_pow;
        Lambda_pow *= Lambda;
    }
    acc1 += acc2;

    if (party == ALICE) {
        ios[0]->send_data(&acc1, sizeof(gf128bit));
        ios[0]->flush();
    } else {
        gf128bit diff;
        ios[0]->recv_data(&diff, sizeof(gf128bit));
        assert(acc1 == diff);
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