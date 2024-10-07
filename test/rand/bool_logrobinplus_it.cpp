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

    // Alice commit the o
    std::vector<Bit> com_o;
    for (size_t i = 0; i < nx; i++) com_o.push_back( Bit(party == ALICE ? wo[i].val : 0, ALICE) );

    // Bob issues random challanges alpha and parties compute its powers
    gf128bit alpha;
    if (party == ALICE) {
		ios[0]->recv_data(&alpha, sizeof(gf128bit));
    } else {
		PRG().random_data(&alpha, sizeof(gf128bit));
		ios[0]->send_data(&alpha, sizeof(gf128bit));	        
        ios[0]->flush();
    }    
    std::vector<gf128bit> alpha_power;
    alpha_power.push_back(gf128bit().unit());
    for (size_t i = 0; i < nx; i++) alpha_power.push_back( alpha_power.back() * alpha );

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

    // prove that 1 out of B is linear function
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

    // Alice and Bob prepare the masks for randomization
    ext_f2 r[log_branch_size+1][2];
    r[log_branch_size][0] = ext_f2::uniform();
    for (size_t i = 0; i < log_branch_size; i++) {
        r[i][0] = ext_f2::uniform();
        r[i][1] = ext_f2::uniform();
    }

    // Alice prepares the coefficients for the final polynomial
    std::vector<ext_f2> poly_coeff;
    gf128bit row2[log_branch_size];
    gf128bit row1[log_branch_size+1];    
    if (party == ALICE) {
        std::vector<std::vector<gf128bit>> final_acc; final_acc.resize(log_branch_size+1, vector<gf128bit>(3));            
        std::vector<gf128bit> tmp_acc; tmp_acc.push_back( gf128bit::unit() );
        for (size_t i = 0; i < log_branch_size; i++) tmp_acc.push_back( gf128bit::zero() );
        compPcoeff(0, id, 0, bdelta, M, final_acc, tmp_acc);
        // cout << final_acc[log_branch_size][2].val << endl;
        assert(final_acc[log_branch_size][2] == gf128bit::zero());

        // Alice add the randomization
        // for the log_branch_size one
        final_acc[log_branch_size][1] += r[log_branch_size][0].val;
        final_acc[log_branch_size][0] += r[log_branch_size][0].key;
        for (size_t i = 0; i < log_branch_size; i++) {
            final_acc[i][2] += r[i][1].val;
            final_acc[i][1] += r[i][0].val + r[i][1].key;
            final_acc[i][0] += r[i][0].key;
        }        

        // Alice commits to the constant terms
        for (size_t i = 0; i <= log_branch_size; i++) {
            ext_f2 tmp = ext_f2::uniform();
            gf128bit diff = tmp.val + final_acc[i][0];
            tmp.val = final_acc[i][0];
            ios[0]->send_data(&diff, sizeof(gf128bit));
            poly_coeff.push_back( tmp );
        }
        ios[0]->flush();

        // Alice sends randomized coefficients on other terms
        for (size_t i = 0; i < log_branch_size; i++) {
            row2[i] = final_acc[i][2];
            row1[i] = final_acc[i][1];
        }
        row1[log_branch_size] = final_acc[log_branch_size][1];
        ios[0]->send_data(&row2, sizeof(gf128bit) * log_branch_size);
        ios[0]->send_data(&row1, sizeof(gf128bit) * (log_branch_size + 1));
        ios[0]->flush();
    } else {
        // Alice commits to the constant terms
        for (size_t i = 0; i <= log_branch_size; i++) {
            ext_f2 tmp = ext_f2::uniform();
            gf128bit diff;
            ios[0]->recv_data(&diff, sizeof(gf128bit));
            tmp.key += gf128bit(delta) * diff;
            poly_coeff.push_back( tmp );
        }

        // Alice sends randomzed coefficients on other terms
        ios[0]->recv_data(&row2, sizeof(gf128bit) * log_branch_size);
        ios[0]->recv_data(&row1, sizeof(gf128bit) * (log_branch_size + 1));
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

    // Bob expands the pathmat
    // Alice only open the "constant" leftover term
    if (party == ALICE) {
        // Alice prepares and opens the last row
        Bit zero(false, PUBLIC);
        ext_f2 acc_poly_coeff;
        acc_poly_coeff.key = gf128bit(zero.bit);
        gf128bit coeff_Lambda = gf128bit::unit();
        for (size_t i = 0; i <= log_branch_size; i++) {
            acc_poly_coeff.key += poly_coeff[i].key * coeff_Lambda;
            acc_poly_coeff.val += poly_coeff[i].val * coeff_Lambda;
            coeff_Lambda *= Lambda;
        }
        ios[0]->send_data(&acc_poly_coeff.val, sizeof(gf128bit));
        ios[0]->send_data(&acc_poly_coeff.key, sizeof(gf128bit));
        ios[0]->flush();
    } else {
        std::vector<gf128bit> row;
        for (size_t i = 0; i < log_branch_size; i++) row.push_back( pathmat_row[i] );
        // Both parties expand the pathmat
        std::vector<gf128bit> expand_vec(branch_size);
        expand_pathmat(0, 0, gf128bit::unit(), row, expand_vec, Lambda);

        // Bob/V computes the polynomial evaluation using K with two ways
        gf128bit acc_K, acc_K_2;
        gf128bit gf_delta(delta); gf128bit gf_delta_2 = gf_delta * gf_delta;
        Bit zero(false, PUBLIC);
        ext_f2 acc_poly_coeff;
        acc_poly_coeff.key = gf128bit(zero.bit);
        for (size_t i = 0; i < branch_size; i++) acc_K += expand_vec[i] * K[i];
        // Bob add the randomization into acc_K
        gf128bit coeff_Lambda = gf128bit::unit();
        for (size_t i = 0; i < log_branch_size; i++) {
            acc_K += coeff_Lambda * gf_delta * r[i][1].key + coeff_Lambda * r[i][0].key; // randomization
            acc_poly_coeff.key = acc_poly_coeff.key + (poly_coeff[i].key * coeff_Lambda);
            acc_K_2 += row1[i] * coeff_Lambda * gf_delta;
            acc_K_2 += row2[i] * coeff_Lambda * gf_delta_2;
            coeff_Lambda *= Lambda;
        }
        acc_K += coeff_Lambda * r[log_branch_size][0].key; // randomization
        acc_K_2 += row1[log_branch_size] * coeff_Lambda * gf_delta;
        acc_poly_coeff.key = acc_poly_coeff.key + (poly_coeff[log_branch_size].key * coeff_Lambda);
        
        // open acc_poly_coeff and add it up to acc_K_2
        gf128bit value, key;
        ios[0]->recv_data(&value, sizeof(gf128bit));
        ios[0]->recv_data(&key, sizeof(gf128bit));
        //cout << acc_poly_coeff.key.val << ' ' << (value * gf_delta + key).val << endl;
        assert( value * gf_delta + key == acc_poly_coeff.key );
        acc_K_2 += value;

        // finally check if two accumulated values are equal
        //cout << acc_K.val << ' ' << acc_K_2.val << endl;
        assert( acc_K == acc_K_2 );
    }



    // accumulate using two ways
    // Bit zero(false, PUBLIC);
    // gf128bit acc1; acc1 = gf128bit( zero.bit );
    // gf128bit acc2; acc2 = gf128bit( zero.bit );
    // for (size_t i = 0; i < branch_size; i++) {
    //     acc1 += bmac[i].key * expand_vec[i];
    // }
    // gf128bit Lambda_pow = gf128bit::unit();
    // for (size_t i = 0; i < log_branch_size; i++) {
    //     acc2 = acc2 + poly_coeff[i].key * Lambda_pow;
    //     Lambda_pow *= Lambda;
    // }
    // acc1 += acc2;

    // if (party == ALICE) {
    //     ios[0]->send_data(&acc1, sizeof(gf128bit));
    //     ios[0]->flush();
    // } else {
    //     gf128bit diff;
    //     ios[0]->recv_data(&diff, sizeof(gf128bit));
    //     assert(acc1 == diff);
    // }

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