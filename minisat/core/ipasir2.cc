// #define __STDC_LIMIT_MACROS
// #define __STDC_FORMAT_MACROS

#include <vector>

#include "Solver.h"

#define l_True (Minisat::lbool((uint8_t)0))
#define l_False (Minisat::lbool((uint8_t)1))
#define l_Undef (Minisat::lbool((uint8_t)2))


class SolverWrapper {
    Minisat::Solver* solver;

    Minisat::vec<Minisat::Lit> assumptions;
    Minisat::vec<Minisat::Lit> clause;

    std::vector<uint8_t> is_failed_assumption;

    enum solver_state {
        STATE_INPUT,
        STATE_SAT,
        STATE_UNSAT
    } state;

    void createVarIfNotExists(int32_t lit) {
        while (abs(lit) > solver->nVars()) {
            (void)solver->newVar();
        }
        if (abs(lit)*2 > is_failed_assumption.size()) {
            is_failed_assumption.resize(abs(lit)*2, 0);
        }
    }

    Minisat::Lit toMinisatLit(int32_t lit) {
        return Minisat::mkLit(Minisat::Var(abs(lit) - 1), (lit < 0));
    }
    
public:
    SolverWrapper() : assumptions(), clause(), is_failed_assumption(), state(STATE_INPUT) {
        solver = new Minisat::Solver();
    }

    ~SolverWrapper() { 
        delete solver;
    }

    void add(int32_t lit) {
        if (state == STATE_UNSAT) {
            std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);
        }
        state = STATE_INPUT;
        createVarIfNotExists(lit);
        if (lit == 0) {
            solver->addClause(clause);
            clause.clear();
        } 
        else {
            clause.push(toMinisatLit(lit));
        }
    }

    void assume(int32_t lit) {
        if (state == STATE_UNSAT) {
            std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);
        }
        state = STATE_INPUT;
        createVarIfNotExists(lit);
        assumptions.push(toMinisatLit(lit));
    }

    int solve() {
        Minisat::lbool res = solver->solveLimited(assumptions);
        assumptions.clear();
        std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);

        if (res == l_True) {
            state = STATE_SAT;
            return 10;
        } 
        else if (res == l_False) {
            for (int i = 0; i < solver->conflict.size(); i++) {
                Minisat::Lit failed = solver->conflict[i];
                is_failed_assumption[failed.x] = 1;
            }
            state = STATE_UNSAT;
            return 20;
        } 
        else if (res == l_Undef) {
            state = STATE_INPUT;
            return 0;
        }
        return -1;
    }

    int val(int32_t lit) {
        if (state != STATE_SAT) {
            return 0;
        }
        Minisat::lbool res = solver->modelValue(toMinisatLit(lit));
        return (res == l_True) ? lit : -lit;
    }

    int failed(int32_t lit) {
        if (state != STATE_UNSAT) {
            return 0;
        }
        return is_failed_assumption[toMinisatLit(-lit).x];
    }

    void setTermCallback(void* state, int (*terminate)(void* state)) {
        solver->setTermCallback(state, terminate);
    }

    void setLearnCallback(void* state, void (*learned)(void* state, int32_t* clause)) {
        solver->setLearnCallback(state, learned);
    }
};

extern "C" {
    #include "ipasir2.h"

    static const char* sig = "Minisat 2.2.0";

    ipasir2_errorcode ipasir2_signature(const char** signature) {
        *signature = sig;
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_init(void** solver) {
        *solver = (void*)new SolverWrapper();
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_release(void* solver) {
        delete (SolverWrapper*)solver;
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_options(void* solver, ipasir2_option const** options) {
        ipasir2_option* solver_options = new ipasir2_option[1];
        solver_options[0] = { nullptr, INT, 0, 0 };
        *options = solver_options;
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_set_option(void* solver, const char* name, ipasir2_option_value value) {
        return IPASIR_E_OPTION_UNKNOWN;
    }

    ipasir2_errorcode ipasir2_add(void* solver, int32_t lit_or_zero) {
        ((SolverWrapper*)solver)->add(lit_or_zero);
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_assume(void* solver, int32_t lit) {
        ((SolverWrapper*)solver)->assume(lit);
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_solve(void* solver, int32_t* status) {
        *status = ((SolverWrapper*)solver)->solve();
        if (*status == -1) {
            return IPASIR_E_UNKNOWN;
        }        
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_val(void* solver, int32_t lit, int32_t* val) {
        *val = ((SolverWrapper*)solver)->val(lit);
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_failed(void* solver, int32_t lit, int32_t* failed) {
        *failed = ((SolverWrapper*)solver)->failed(lit);
        return IPASIR_E_OK;
    }

    // TODO
    ipasir2_errorcode ipasir2_assignment_size(void* solver, int32_t* size) {
        return IPASIR_E_UNSUPPORTED;
    }

    // TODO
    ipasir2_errorcode ipasir2_assignment(void* solver, int32_t index, int32_t* assignment) {
        return IPASIR_E_UNSUPPORTED;
    }

    ipasir2_errorcode ipasir2_set_terminate(void* solver, void* state, int (*terminate)(void* state)) {
        ((SolverWrapper*)solver)->setTermCallback(state, terminate);
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_set_learn(void* solver, void* state, void (*learned)(void* state, int32_t* clause)) {
        ((SolverWrapper*)solver)->setLearnCallback(state, learned);
        return IPASIR_E_OK;
    }

    // TODO
    ipasir2_errorcode ipasir2_set_import_redundant_clause(void* solver, void* state, void (*import)(void* state, int32_t** clause)) {
        return IPASIR_E_UNSUPPORTED;
    }
};
