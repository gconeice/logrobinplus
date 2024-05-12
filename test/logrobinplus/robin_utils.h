#ifndef ZKCPU_H__
#define ZKCPU_H__

#include <vector>
#include <random>
#include <iostream>
#include <cassert>
#include <string>
#include <fstream>

// Use (void) to silence unused warnings.
#define assertm(exp, msg) assert(((void)msg, exp))

#include "emp-zk/emp-zk.h"
#include "emp-tool/emp-tool.h"
#if defined(__linux__)
	#include <sys/time.h>
	#include <sys/resource.h>
#elif defined(__APPLE__)
	#include <unistd.h>
	#include <sys/resource.h>
	#include <mach/mach.h>
#endif

class f2 {
public:
    bool val;

    f2() {val = 0;}
    f2(bool val) : val(val) {}

    static f2 minor(bool x) {
        return f2(x^1);
    }

    f2 minor() {
        return f2(val^1);
    }

    f2 & operator+= (f2 const & rhs) { 
        val ^= rhs.val; 
        return *this; 
    }
    f2 & operator+= (f2 && rhs) { 
        val ^= rhs.val;
        return *this;
    }
    f2 & operator*= (f2 const & rhs) {
        val &= rhs.val;
        return *this;
    }
    f2 & operator*= (f2 && rhs) {
        val &= rhs.val;
        return *this;
    }

    f2 operator+(f2 rhs) &  { return rhs += *this; }
    f2 operator+(f2 rhs) && { return rhs += std::move(*this); }
    f2 operator*(f2 rhs) &  { return rhs *= *this; }
    f2 operator*(f2 rhs) && { return rhs *= std::move(*this); }

    static f2 unit() {
        return f2(1);
    }

    static f2 zero() {
        return f2(0);
    }
};

class gf128bit {
public:
    block val;

    gf128bit() {val = makeBlock(0, 0);}
    gf128bit(block val) : val(val) {}

    static gf128bit minor(block x) {
        return gf128bit(x);
    }

    gf128bit & operator+= (gf128bit const & rhs) { 
        val ^= rhs.val; 
        return *this; 
    }
    gf128bit & operator+= (gf128bit && rhs) { 
        val ^= rhs.val;
        return *this;
    }
    gf128bit & operator*= (gf128bit const & rhs) {
        block tmp;
        gfmul(val, rhs.val, &tmp);
        val = tmp;
        return *this;
    }
    gf128bit & operator*= (gf128bit && rhs) {
        block tmp;
        gfmul(val, rhs.val, &tmp);
        val = tmp;
        return *this;
    }

    gf128bit operator+(gf128bit rhs) &  { return rhs += *this; }
    gf128bit operator+(gf128bit rhs) && { return rhs += std::move(*this); }
    gf128bit operator*(gf128bit rhs) &  { return rhs *= *this; }
    gf128bit operator*(gf128bit rhs) && { return rhs *= std::move(*this); }

    static gf128bit unit() {
        return gf128bit( makeBlock(0, 1) );
    }

    static gf128bit zero() {
        return gf128bit( makeBlock(0, 0) );
    }
};

class ext_f2{
public:
    gf128bit val;
    gf128bit key;
    static ext_f2 uniform() {
        ext_f2 res;
        emp::zkp_get_ope<BoolIO<NetIO>>(res.key.val, res.val.val);
        return res;
    }
};

class f61 {
public:
    uint64_t val;

    f61(uint64_t val) : val(val) {}
    f61() : val(0) {}

    static f61 unit() {
        return f61(1);
    }
    static f61 zero() {
        return f61(0);
    }
    static f61 minor(uint64_t x) {
        return f61(PR - x);
    }

    f61 & operator+= (f61 const & rhs) { 
        val = add_mod(val, rhs.val);         
        return *this; 
    }
    f61 & operator+= (f61 && rhs) { 
        val = add_mod(val, rhs.val);
        return *this;
    }
    f61 & operator*= (f61 const & rhs) {
        val = mult_mod(val, rhs.val);
        return *this;
    }
    f61 & operator*= (f61 && rhs) {
        val = mult_mod(val, rhs.val);
        return *this;
    }
    f61 operator+(f61 rhs) &  { return rhs += *this; }
    f61 operator+(f61 rhs) && { return rhs += std::move(*this); }
    f61 operator*(f61 rhs) &  { return rhs *= *this; }
    f61 operator*(f61 rhs) && { return rhs *= std::move(*this); }    
};

struct f61Triple {
    f61 coef[3];
};

enum OPTYPE {
    ADD, MUL
};

class BaseOp {
public:
    OPTYPE op;
    std::size_t l,r;
    BaseOp(OPTYPE op, std::size_t l, std::size_t r) : op(op), l(l), r(r) {}
    BaseOp() {}
};

class Circuit{
    std::size_t nin; // number of inputs
    std::size_t nx; // number of mults
    std::vector<BaseOp> bank;

public:
    Circuit(std::size_t nin, std::size_t nx) : nin(nin), nx(nx) {}

    void rand_cir(std::mt19937 &gen) {
        std::uniform_int_distribution<> distr(0, nx*100);
        std::size_t cur = nx;
        while (cur) {
            std::size_t last = bank.size() + nin;
            std::size_t l = distr(gen) % last;
            std::size_t r = distr(gen) % last;
            if (l > r) std::swap(l, r);
            OPTYPE optype = distr(gen) % 2 ? OPTYPE::ADD : OPTYPE::MUL;
            bank.push_back(BaseOp(optype, l, r));
            if (optype == OPTYPE::MUL) {                
                cur--;
            }            
        }
    }

    void test_out() {
        std::cout << bank[0].l << ' ' << bank[0].r << std::endl;
    }

    f61 f61_gen_wit(std::mt19937 &gen, std::vector<f61> &in, std::vector<f61> &l, std::vector<f61> &r, std::vector<f61> &o) {
        std::uniform_int_distribution<> distr(0, 100000000);
        std::vector<f61> w;
        for (size_t i = 0; i < nin; i++) {
            std::size_t in_val = distr(gen);
            w.push_back(f61(in_val));
            in.push_back(f61(in_val));
        }
        for (size_t i = 0; i < bank.size(); i++) {
            if (bank[i].op == OPTYPE::ADD) {
                f61 new_val = w[ bank[i].l ] + w[ bank[i].r ];
                w.push_back(new_val);
            } else {
                f61 new_val = w[ bank[i].l ] * w[ bank[i].r ];
                w.push_back(new_val);
                l.push_back(w[bank[i].l]);
                r.push_back(w[bank[i].r]);
                o.push_back(new_val);
            }
        }
        return w[w.size()-1];
    }

    f2 f2_gen_wit(std::mt19937 &gen, std::vector<f2> &in, std::vector<f2> &l, std::vector<f2> &r, std::vector<f2> &o) {
        std::uniform_int_distribution<> distr(0, 1);
        std::vector<f2> w;
        for (size_t i = 0; i < nin; i++) {
            std::size_t in_val = distr(gen);
            w.push_back(f2(in_val));
            in.push_back(f2(in_val));
        }
        for (size_t i = 0; i < bank.size(); i++) {
            if (bank[i].op == OPTYPE::ADD) {
                f2 new_val = w[ bank[i].l ] + w[ bank[i].r ];
                w.push_back(new_val);
            } else {
                f2 new_val = w[ bank[i].l ] * w[ bank[i].r ];
                w.push_back(new_val);
                l.push_back(w[bank[i].l]);
                r.push_back(w[bank[i].r]);
                o.push_back(new_val);
            }
        }
        return w[w.size()-1];
    }

    IntFp f61_zk_eval(std::vector<IntFp> &in) {
        assert(in.size() == nin);
        std::vector<IntFp> w;
        for (size_t i = 0; i < nin; i++) w.push_back(in[i]);
        for (size_t i = 0; i < bank.size(); i++) {
            if (bank[i].op == OPTYPE::ADD) w.push_back( w[bank[i].l] + w[bank[i].r] );
            else w.push_back( w[bank[i].l] * w[bank[i].r] );
        }
        return w[w.size() - 1];
    }

    // this function accumulates the robin's style linear combination
    // arith
    IntFp robin_acc(std::vector<IntFp> &in, std::vector<IntFp> &l, std::vector<IntFp> &r, std::vector<IntFp> &o, std::vector<f61> &coeff, uint64_t final_res) {
        assert(in.size() == nin);
        assert(l.size() == nx);
        assert(r.size() == nx);
        assert(o.size() == nx);
        assert(coeff.size() == 2*nx+1);

        IntFp acc_res = IntFp(0, PUBLIC);

        int acc_id = 0;
        std::vector<IntFp> w;
        for (size_t i = 0; i < nin; i++) w.push_back(in[i]);
        for (size_t i = 0; i < bank.size(); i++) {
            if (bank[i].op == OPTYPE::ADD) w.push_back( w[bank[i].l] + w[bank[i].r] );
            else {
                acc_res = acc_res + (w[bank[i].l] + l[acc_id].negate()) * coeff[2*acc_id].val;
                acc_res = acc_res + (w[bank[i].r] + r[acc_id].negate()) * coeff[2*acc_id+1].val;
                w.push_back( o[acc_id++] );
            }
        }

        // put up the output
        acc_res = acc_res + (w.back() + final_res) * coeff.back().val;
        return acc_res;
    }

    // this function accumulates the robin's style linear combination
    // bool
    ext_f2 robin_acc(std::vector<Bit> &in, std::vector<Bit> &l, std::vector<Bit> &r, std::vector<Bit> &o, std::vector<gf128bit> &coeff, f2 final_res) {
        assert(in.size() == nin);
        assert(l.size() == nx);
        assert(r.size() == nx);
        assert(o.size() == nx);
        assert(coeff.size() == 2*nx+1);

        ext_f2 acc_res;

        int acc_id = 0;
        std::vector<Bit> w;
        for (size_t i = 0; i < nin; i++) w.push_back(in[i]);
        for (size_t i = 0; i < bank.size(); i++) {
            if (bank[i].op == OPTYPE::ADD) w.push_back( w[bank[i].l] ^ w[bank[i].r] );
            else {
                // acc_res = acc_res + (w[bank[i].l] + l[acc_id].negate()) * coeff[2*acc_id].val;
                // acc_res = acc_res + (w[bank[i].r] + r[acc_id].negate()) * coeff[2*acc_id+1].val;
                Bit tmpbit;
                tmpbit = w[bank[i].l] ^ l[acc_id];
                acc_res.key = acc_res.key + gf128bit(tmpbit.bit) * coeff[2*acc_id];
                if (getLSB(tmpbit.bit)) acc_res.val = acc_res.val + coeff[2*acc_id];
                tmpbit = w[bank[i].r] ^ r[acc_id];
                acc_res.key = acc_res.key + gf128bit(tmpbit.bit) * coeff[2*acc_id+1];
                if (getLSB(tmpbit.bit)) acc_res.val = acc_res.val + coeff[2*acc_id+1];
                w.push_back( o[acc_id++] );
            }
        }

        // put up the output
        Bit tmpbit = w.back() ^ Bit(final_res.val, PUBLIC);
        acc_res.key = acc_res.key + gf128bit(tmpbit.bit) * coeff.back();
        if (getLSB(tmpbit.bit)) acc_res.val = acc_res.val + coeff.back();
        return acc_res;
    }    



    // this function accumulates the robinplus's styple quadratic correlation
    // this is for P or Alice
    f61Triple robinplus_acc_P(std::vector<IntFp> &in, std::vector<IntFp> &o, std::vector<f61> &coeff, uint64_t final_res) {
        assert(in.size() == nin);
        assert(o.size() == nx);
        assert(coeff.size() == nx+1);
        f61Triple res;
        res.coef[0].val = res.coef[1].val = res.coef[2].val = 0;

        int acc_id = 0;
        std::vector<IntFp> w;
        for (size_t i = 0; i < nin; i++) w.push_back(in[i]);
        for (size_t i = 0; i < bank.size(); i++) {
            if (bank[i].op == OPTYPE::ADD) w.push_back( w[bank[i].l] + w[bank[i].r] );
            else {
                res.coef[2] += coeff[acc_id] * ( f61( HIGH64(w[bank[i].l].value) ) * f61( HIGH64(w[bank[i].r].value) ) + f61::minor( HIGH64(o[acc_id].value) ) );
                res.coef[1] += coeff[acc_id] * ( f61::minor( HIGH64(w[bank[i].l].value) ) * f61( LOW64(w[bank[i].r].value) ) + f61::minor( HIGH64(w[bank[i].r].value) ) * f61( LOW64(w[bank[i].l].value) ) + f61( LOW64(o[acc_id].value) ) );
                res.coef[0] += coeff[acc_id] * ( f61( LOW64(w[bank[i].l].value) ) * f61( LOW64(w[bank[i].r].value) ) );
                w.push_back( o[acc_id++] );
            }
        }

        // put up the output
        IntFp fout = w.back() + final_res;
        IntFp zero(0, PUBLIC);
        res.coef[2] += coeff[acc_id] * ( f61( HIGH64(fout.value) ) * f61( HIGH64(fout.value) ) + f61::minor( HIGH64(zero.value) ) );
        res.coef[1] += coeff[acc_id] * ( f61::minor( HIGH64(fout.value) ) * f61( LOW64(fout.value) ) + f61::minor( HIGH64(fout.value) ) * f61( LOW64(fout.value) ) + f61( LOW64(zero.value) ) );
        res.coef[0] += coeff[acc_id] * ( f61( LOW64(fout.value) ) * f61( LOW64(fout.value) ) );

        return res;
    }

    // this function accumulates the robinplus's styple quadratic correlation
    // this is for V or Bob
    f61 robinplus_acc_V(std::vector<IntFp> &in, std::vector<IntFp> &o, std::vector<f61> &coeff, uint64_t final_res, f61 delta) {
        assert(in.size() == nin);
        assert(o.size() == nx);
        assert(coeff.size() == nx+1);
        f61 res = f61::zero();

        int acc_id = 0;
        std::vector<IntFp> w;
        for (size_t i = 0; i < nin; i++) w.push_back(in[i]);
        for (size_t i = 0; i < bank.size(); i++) {
            if (bank[i].op == OPTYPE::ADD) w.push_back( w[bank[i].l] + w[bank[i].r] );
            else {
                res += coeff[acc_id] * ( f61( LOW64(w[bank[i].l].value) ) * f61( LOW64(w[bank[i].r].value) ) + f61( LOW64(o[acc_id].value) ) * delta );
                w.push_back( o[acc_id++] );
            }
        }

        // put up the output
        IntFp fout = w.back() + final_res;
        IntFp zero(0, PUBLIC);
        res += coeff[acc_id] * ( f61( LOW64(fout.value) ) * f61( LOW64(fout.value) ) + f61( LOW64(zero.value) ) * delta );
        return res;
    }

};

// this procedure is used to prove that all the elements inside IT-MACs \vec{x} is a 01 vector
// the IT version
void prove01vector_it(int party, std::vector<IntFp> x, f61 delta) {
    // Bob issues random challanges alpha
    uint64_t alpha;
    if (party == ALICE) {
		ZKFpExec::zk_exec->recv_data(&alpha, sizeof(uint64_t));
        alpha = alpha % PR; // to prevent cheating V
    } else {
		PRG().random_data(&alpha, sizeof(uint64_t));
		alpha = alpha % PR;
		ZKFpExec::zk_exec->send_data(&alpha, sizeof(uint64_t));	        
    }    
    f61 f61_alpha = f61(alpha);

    if (party == ALICE) {
        f61 C1 = f61::zero();
        f61 C0 = f61::zero();
        f61 pow_alpha = f61::unit();
        for (size_t i = 0; i < x.size(); i++) {
            IntFp xminor1 = x[i] + (PR-1);
            C1 += pow_alpha * ( f61( LOW64(x[i].value) ) * f61( HIGH64(xminor1.value) ) + f61( LOW64(xminor1.value) ) * f61( HIGH64(x[i].value) ) );
            C0 += pow_alpha * ( f61( LOW64(x[i].value) ) * f61( LOW64(xminor1.value) ) );
            pow_alpha *= f61_alpha;
        }
        __uint128_t random_mask = ZKFpExec::zk_exec->get_one_role();
        C1 += f61( HIGH64(random_mask) );
        C0 += f61( LOW64(random_mask) );
        ZKFpExec::zk_exec->send_data(&C1, sizeof(f61));
        ZKFpExec::zk_exec->send_data(&C0, sizeof(f61));

    } else {
        f61 expected_proof = f61::zero();
        f61 pow_alpha = f61::unit();
        for (size_t i = 0; i < x.size(); i++) {
            IntFp xminor1 = x[i] + (PR-1);
            expected_proof += pow_alpha * ( f61( LOW64(x[i].value) ) * f61( LOW64(xminor1.value) ) );
            pow_alpha *= f61_alpha;
        }
        __uint128_t random_mask = ZKFpExec::zk_exec->get_one_role();
        expected_proof += f61( LOW64(random_mask) );
        f61 C1, C0;
        ZKFpExec::zk_exec->recv_data(&C1, sizeof(f61));
        ZKFpExec::zk_exec->recv_data(&C0, sizeof(f61));
        f61 check = f61::minor(C1.val) * delta + C0 + f61::minor(expected_proof.val);
        assertm(check.val == 0, "prove01 fails! P is cheating!");
    }
}


// this procedure is used to prove that all the elements inside IT-MACs \vec{x} is a 01 vector
// the RO version
void prove01vector_ro(int party, std::vector<IntFp> x, f61 delta) {
    // Bob issues random challenges via PRG over a seed
    block alpha_seed; 
    if (party == ALICE) {
		ZKFpExec::zk_exec->recv_data(&alpha_seed, sizeof(block));
    } else {
        PRG().random_block(&alpha_seed, 1);
        ZKFpExec::zk_exec->send_data(&alpha_seed, sizeof(block));
    }
    PRG prg_alpha(&alpha_seed);

    if (party == ALICE) {
        f61 C1 = f61::zero();
        f61 C0 = f61::zero();
        for (size_t i = 0; i < x.size(); i++) {
            block tmptmp;
            prg_alpha.random_block(&tmptmp, 1);
            f61 pow_alpha( LOW64(tmptmp) % PR );
            IntFp xminor1 = x[i] + (PR-1);
            C1 += pow_alpha * ( f61( LOW64(x[i].value) ) * f61( HIGH64(xminor1.value) ) + f61( LOW64(xminor1.value) ) * f61( HIGH64(x[i].value) ) );
            C0 += pow_alpha * ( f61( LOW64(x[i].value) ) * f61( LOW64(xminor1.value) ) );
        }
        __uint128_t random_mask = ZKFpExec::zk_exec->get_one_role();
        C1 += f61( HIGH64(random_mask) );
        C0 += f61( LOW64(random_mask) );
        ZKFpExec::zk_exec->send_data(&C1, sizeof(f61));
        ZKFpExec::zk_exec->send_data(&C0, sizeof(f61));

    } else {
        f61 expected_proof = f61::zero();
        for (size_t i = 0; i < x.size(); i++) {
            block tmptmp;
            prg_alpha.random_block(&tmptmp, 1);
            f61 pow_alpha( LOW64(tmptmp) % PR );
            IntFp xminor1 = x[i] + (PR-1);
            expected_proof += pow_alpha * ( f61( LOW64(x[i].value) ) * f61( LOW64(xminor1.value) ) );
        }
        __uint128_t random_mask = ZKFpExec::zk_exec->get_one_role();
        expected_proof += f61( LOW64(random_mask) );
        f61 C1, C0;
        ZKFpExec::zk_exec->recv_data(&C1, sizeof(f61));
        ZKFpExec::zk_exec->recv_data(&C0, sizeof(f61));
        f61 check = f61::minor(C1.val) * delta + C0 + f61::minor(expected_proof.val);
        assertm(check.val == 0, "prove01 fails! P is cheating!");
    }
}


// procedure for (LogRobin) p to compute the coefficients
void compPcoeff(size_t depth, size_t id, size_t cur, std::vector<IntFp> &delta, std::vector<IntFp> &bmac, std::vector<f61> &final_acc, std::vector<f61> &tmp_acc) {
    // base case, accumulate
    if (depth == delta.size()) {
        f61 cur_value( HIGH64(bmac[cur].value) );
        for (size_t i = 0; i < final_acc.size(); i++) final_acc[i] += cur_value * tmp_acc[i];
        return;
    }
    size_t last_id = id % 2;
    std::vector<f61> tmp;
    // go up, i.e., cur = cur*2
    tmp.clear();
    if (last_id == 0) { // up = X-\delta_depth
        tmp.push_back( f61::zero() );
        for (size_t i = 0; i < tmp_acc.size() - 1; i++) tmp.push_back( tmp_acc[i] );
        for (size_t i = 0; i < tmp_acc.size(); i++) tmp[i] += tmp_acc[i] * f61( PR - HIGH64(delta[depth].value) );
    } else { // up = -\delta_depth
        for (size_t i = 0; i < tmp_acc.size(); i++) tmp.push_back( tmp_acc[i] * f61( PR - HIGH64(delta[depth].value) ) );
    }
    compPcoeff(depth+1, id >> 1, cur, delta, bmac, final_acc, tmp);

    // go down, i.e., cur = cur*2+1
    tmp.clear();
    if (last_id == 0) { // down = \delta_depth
        for (size_t i = 0; i < tmp_acc.size(); i++) tmp.push_back( tmp_acc[i] * f61( HIGH64(delta[depth].value) ) );
    } else { // down = X+\delta_depth
        tmp.push_back( f61::zero() );
        for (size_t i = 0; i < tmp_acc.size() - 1; i++) tmp.push_back( tmp_acc[i] );
        for (size_t i = 0; i < tmp_acc.size(); i++) tmp[i] += tmp_acc[i] * f61( HIGH64(delta[depth].value) );
    }
    compPcoeff(depth+1, id >> 1, cur + (1 << depth), delta, bmac, final_acc, tmp);
}

// procedure for (LogRobin++) p to compute the coefficients
void compPcoeff(size_t depth, size_t id, size_t cur, std::vector<IntFp> &delta, std::vector<f61Triple> &M, std::vector<std::vector<f61>> &final_acc, std::vector<f61> &tmp_acc) {
    // base case, accumulate
    if (depth == delta.size()) {
        f61 cur_value = M[cur].coef[2];
        for (size_t i = 0; i < tmp_acc.size(); i++) final_acc[i][2] += cur_value * tmp_acc[i];
        cur_value = M[cur].coef[1];
        for (size_t i = 0; i < tmp_acc.size(); i++) final_acc[i][1] += cur_value * tmp_acc[i];    
        cur_value = M[cur].coef[0];
        for (size_t i = 0; i < tmp_acc.size(); i++) final_acc[i][0] += cur_value * tmp_acc[i];        
        return;
    }
    size_t last_id = id % 2;
    std::vector<f61> tmp;
    // go up, i.e., cur = cur*2
    tmp.clear();
    if (last_id == 0) { // up = X-\delta_depth
        tmp.push_back( f61::zero() );
        for (size_t i = 0; i < tmp_acc.size() - 1; i++) tmp.push_back( tmp_acc[i] );
        for (size_t i = 0; i < tmp_acc.size(); i++) tmp[i] += tmp_acc[i] * f61( PR - HIGH64(delta[depth].value) );
    } else { // up = -\delta_depth
        for (size_t i = 0; i < tmp_acc.size(); i++) tmp.push_back( tmp_acc[i] * f61( PR - HIGH64(delta[depth].value) ) );
    }
    compPcoeff(depth+1, id >> 1, cur, delta, M, final_acc, tmp);

    // go down, i.e., cur = cur*2+1
    tmp.clear();
    if (last_id == 0) { // down = \delta_depth
        for (size_t i = 0; i < tmp_acc.size(); i++) tmp.push_back( tmp_acc[i] * f61( HIGH64(delta[depth].value) ) );
    } else { // down = X+\delta_depth
        tmp.push_back( f61::zero() );
        for (size_t i = 0; i < tmp_acc.size() - 1; i++) tmp.push_back( tmp_acc[i] );
        for (size_t i = 0; i < tmp_acc.size(); i++) tmp[i] += tmp_acc[i] * f61( HIGH64(delta[depth].value) );
    }
    compPcoeff(depth+1, id >> 1, cur + (1 << depth), delta, M, final_acc, tmp);
}

// procedure for parties to expand the pathmat
void expand_pathmat(size_t depth, size_t cur, f61 acc, std::vector<f61> &row, std::vector<f61> &expand_vec, f61 &Lambda) {
    // base case, accumulate
    if (depth == row.size()) {
        expand_vec[cur] = acc;
        return;
    }
    // go up
    expand_pathmat(depth+1, cur, acc * (Lambda + f61::minor(row[depth].val)), row, expand_vec, Lambda);
    // go down
    expand_pathmat(depth+1, cur + (1 << depth), acc * row[depth], row, expand_vec, Lambda);
}

// this function proves the multiplication is 0
// Boolean -- extension over GF(2^128), it version
void prove_product_zero_it(BoolIO<NetIO> *ios[1], int party, std::vector<ext_f2> &x) {
    size_t x_size = x.size();
    assert(x_size > 1);
    std::vector<ext_f2> inter;
    for (size_t i = 0; i < x_size-2; i++) inter.push_back( ext_f2::uniform() );
    gf128bit delta = gf128bit( emp::get_bool_delta<BoolIO<NetIO>>(party) );

    // ALICE/P commits to the intermedia values
    if (party == ALICE) {
        gf128bit acc = x[0].val;
        for (size_t i = 1; i < x_size-1; i++) {
            acc *= x[i].val;
            gf128bit diff = acc + inter[i-1].val;
            inter[i-1].val = acc;
            ios[0]->send_data(&diff, sizeof(gf128bit));
        }
        ios[0]->flush();
    } else {
        for (size_t i = 0; i < x_size-2; i++) {
            gf128bit diff;
            ios[0]->recv_data(&diff, sizeof(gf128bit));
            inter[i].key += diff * delta;
        }
    }

    // finally, add a 0 inside inter
    Bit zero(false, PUBLIC);
    if (party == ALICE) {
        ext_f2 tmp;
        tmp.key = zero.bit;
        inter.push_back(tmp);
    } else {
        ext_f2 tmp;
        tmp.key = zero.bit;
        inter.push_back(tmp);
    }

    // V issues random challenge to linearly combine all LPZKs
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
    for (size_t i = 0; i < x_size-2; i++) alpha_power.push_back( alpha_power.back() * alpha );

    // LPZK
    if (party == ALICE) {
        gf128bit C1, C0;

        // the first multi
        // x[0] * x[1] = inter[0]
        C1 += x[0].val * x[1].key + x[0].key * x[1].val + inter[0].key;
        C0 += x[0].key * x[1].key;

        for (size_t i = 1; i < x_size-1; i++) {
            // inter[i-1] * x[i+1] = inter[i]
            C1 += alpha_power[i] * (inter[i-1].val * x[i+1].key + inter[i-1].key * x[i+1].val + inter[i].key);
            C0 += alpha_power[i] * (inter[i-1].key * x[i+1].key);
        }

        // randomization
        ext_f2 pad = ext_f2::uniform();
        C1 += pad.val;
        C0 += pad.key;

        ios[0]->send_data(&C1, sizeof(gf128bit));
        ios[0]->send_data(&C0, sizeof(gf128bit));
        ios[0]->flush();        
    } else {
        gf128bit A, C1, C0;

        // the first multi
        // x[0] * x[1] = inter[0]
        A += x[0].key * x[1].key + inter[0].key * delta;

        for (size_t i = 1; i < x_size-1; i++) {
            // inter[i-1] * x[i+1] = inter[i];
            A += alpha_power[i] * (inter[i-1].key * x[i+1].key + inter[i].key * delta);
        }

        // randomization
        ext_f2 pad = ext_f2::uniform();
        A = A + pad.key;

        ios[0]->recv_data(&C1, sizeof(gf128bit));
        ios[0]->recv_data(&C0, sizeof(gf128bit));

        // Check equlity
        // std::cout << (C1*delta + C0).val << ' '  << A.val << std::endl;
        assert(C1*delta + C0 == A);
    }

}

// this function proves the multiplication is 0
// Boolean -- extension over GF(2^128), RO version
void prove_product_zero_ro(BoolIO<NetIO> *ios[1], int party, std::vector<ext_f2> &x) {
    size_t x_size = x.size();
    assert(x_size > 1);
    std::vector<ext_f2> inter;
    for (size_t i = 0; i < x_size-2; i++) inter.push_back( ext_f2::uniform() );
    gf128bit delta = gf128bit( emp::get_bool_delta<BoolIO<NetIO>>(party) );

    // ALICE/P commits to the intermedia values
    if (party == ALICE) {
        gf128bit acc = x[0].val;
        for (size_t i = 1; i < x_size-1; i++) {
            acc *= x[i].val;
            gf128bit diff = acc + inter[i-1].val;
            inter[i-1].val = acc;
            ios[0]->send_data(&diff, sizeof(gf128bit));
        }
        ios[0]->flush();
    } else {
        for (size_t i = 0; i < x_size-2; i++) {
            gf128bit diff;
            ios[0]->recv_data(&diff, sizeof(gf128bit));
            inter[i].key += diff * delta;
        }
    }

    // finally, add a 0 inside inter
    Bit zero(false, PUBLIC);
    if (party == ALICE) {
        ext_f2 tmp;
        tmp.key = zero.bit;
        inter.push_back(tmp);
    } else {
        ext_f2 tmp;
        tmp.key = zero.bit;
        inter.push_back(tmp);
    }

    // V issues random challenge to linearly combine all LPZKs
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
    for (size_t i = 0; i < x_size-1; i++) {
        block tmptmp;
        prg_alpha.random_block(&tmptmp, 1);
        alpha_power.push_back( gf128bit(tmptmp) );
    }    

    // LPZK
    if (party == ALICE) {
        gf128bit C1, C0;

        // the first multi
        // x[0] * x[1] = inter[0]
        C1 += alpha_power[0] * (x[0].val * x[1].key + x[0].key * x[1].val + inter[0].key);
        C0 += alpha_power[0] * x[0].key * x[1].key;

        for (size_t i = 1; i < x_size-1; i++) {
            // inter[i-1] * x[i+1] = inter[i]
            C1 += alpha_power[i] * (inter[i-1].val * x[i+1].key + inter[i-1].key * x[i+1].val + inter[i].key);
            C0 += alpha_power[i] * (inter[i-1].key * x[i+1].key);
        }

        // randomization
        ext_f2 pad = ext_f2::uniform();
        C1 += pad.val;
        C0 += pad.key;

        ios[0]->send_data(&C1, sizeof(gf128bit));
        ios[0]->send_data(&C0, sizeof(gf128bit));
        ios[0]->flush();        
    } else {
        gf128bit A, C1, C0;

        // the first multi
        // x[0] * x[1] = inter[0]
        A += alpha_power[0] * (x[0].key * x[1].key + inter[0].key * delta);

        for (size_t i = 1; i < x_size-1; i++) {
            // inter[i-1] * x[i+1] = inter[i];
            A += alpha_power[i] * (inter[i-1].key * x[i+1].key + inter[i].key * delta);
        }

        // randomization
        ext_f2 pad = ext_f2::uniform();
        A = A + pad.key;

        ios[0]->recv_data(&C1, sizeof(gf128bit));
        ios[0]->recv_data(&C0, sizeof(gf128bit));

        // Check equlity
        // std::cout << (C1*delta + C0).val << ' '  << A.val << std::endl;
        assert(C1*delta + C0 == A);
    }

}

#endif