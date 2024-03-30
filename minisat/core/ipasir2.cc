// #define __STDC_LIMIT_MACROS
// #define __STDC_FORMAT_MACROS


#include <limits>
#include <vector>
#include "Solver.h"
#include "ipasir2.h"


#define l_True (Minisat::lbool((uint8_t)0))
#define l_False (Minisat::lbool((uint8_t)1))
#define l_Undef (Minisat::lbool((uint8_t)2))


class SolverWrapper {
    Minisat::Solver* solver;

    Minisat::vec<Minisat::Lit> assumptions;
    Minisat::vec<Minisat::Lit> clause;

    std::vector<uint8_t> is_failed_assumption;

    ipasir2_state state;

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
    SolverWrapper() : assumptions(), clause(), is_failed_assumption(), state(IPASIR2_S_INPUT) {
        solver = new Minisat::Solver();
    }

    ~SolverWrapper() { 
        delete solver;
    }

    void add(int32_t lit) {
        if (state == IPASIR2_S_UNSAT) {
            std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);
        }
        state = IPASIR2_S_INPUT;
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
        if (state == IPASIR2_S_UNSAT) {
            std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);
        }
        state = IPASIR2_S_INPUT;
        createVarIfNotExists(lit);
        assumptions.push(toMinisatLit(lit));
    }

    int solve() {
        Minisat::lbool res = solver->solveLimited(assumptions);
        assumptions.clear();
        std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);

        if (res == l_True) {
            state = IPASIR2_S_SAT;
            return 10;
        } 
        else if (res == l_False) {
            for (int i = 0; i < solver->conflict.size(); i++) {
                Minisat::Lit failed = solver->conflict[i];
                is_failed_assumption[failed.x] = 1;
            }
            state = IPASIR2_S_UNSAT;
            return 20;
        } 
        else if (res == l_Undef) {
            state = IPASIR2_S_INPUT;
            return 0;
        }
        return -1;
    }

    int val(int32_t lit) {
        if (state != IPASIR2_S_SAT) {
            return 0;
        }
        Minisat::lbool res = solver->modelValue(toMinisatLit(lit));
        return (res == l_True) ? lit : -lit;
    }

    int failed(int32_t lit) {
        if (state != IPASIR2_S_UNSAT) {
            return 0;
        }
        return is_failed_assumption[toMinisatLit(-lit).x];
    }

    void setTermCallback(void* state, int (*terminate)(void* state)) {
        solver->setTermCallback(state, terminate);
    }

    void setLearnCallback(void* state, int32_t max_size, void (*learned)(void* state, int32_t const* clause)) {
        solver->setLearnCallback(state, max_size, learned);
    }
};


extern "C" {

    static const char* sig = "Minisat 2.2.0";

    ipasir2_errorcode ipasir2_signature(const char** signature) {
        *signature = sig;
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_init(void** solver) {
        *solver = (void*)new SolverWrapper();
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_release(void* solver) {
        delete (SolverWrapper*)solver;
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_options(void *solver, ipasir2_option const **options)
    {
        static std::vector<ipasir2_option> const option_defs = {
            {"ipasir.limits.decisions", -1, std::numeric_limits<int64_t>::max(), IPASIR2_S_INPUT, 0, 0,
             reinterpret_cast<void*>(+[](Minisat::Solver *solver, ipasir2_option const *opt, int64_t value) {
                solver->setDecisionBudget(value);
             })
            },
            {"ipasir.limits.conflicts", -1, std::numeric_limits<int64_t>::max(), IPASIR2_S_INPUT, 0, 0,
             reinterpret_cast<void*>(+[](Minisat::Solver *solver, ipasir2_option const *opt, int64_t value) {
                solver->setConfBudget(value);
             })
            },
            {nullptr, 0, 0, IPASIR2_S_CONFIG, 0, 0, nullptr}
        };

        *options = option_defs.data();
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_set_option(void* solver, ipasir2_option const* option, int64_t value, int64_t index) {
        if (option != nullptr && option->handle != nullptr) {
            void (*setter)(Minisat::Solver* solver, ipasir2_option const* opt, int64_t value) = (void (*)(Minisat::Solver* solver, ipasir2_option const* opt, int64_t value))option->handle;
            (*setter)((Minisat::Solver*)solver, option, value);
            return IPASIR2_E_OK;
        }
        return IPASIR2_E_UNSUPPORTED_ARGUMENT;
    }

    ipasir2_errorcode ipasir2_add(void* solver, int32_t const* clause, int32_t len, ipasir2_redundancy type) {
        for (int i = 0; i < len; i++) {
            ((SolverWrapper*)solver)->add(clause[i]);
        }
        ((SolverWrapper*)solver)->add(0);
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_solve(void* solver, int* result, int32_t const* assumps, int32_t len) {
        for (int i = 0; i < len; i++) {
            ((SolverWrapper*)solver)->assume(assumps[i]);
        }
        *result = ((SolverWrapper*)solver)->solve();
        if (*result == -1) {
            return IPASIR2_E_UNKNOWN;
        }        
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_val(void* solver, int32_t lit, int32_t* val) {
        *val = ((SolverWrapper*)solver)->val(lit);
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_failed(void* solver, int32_t lit, int32_t* failed) {
        *failed = ((SolverWrapper*)solver)->failed(lit);
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_set_terminate(void* solver, void* state, int (*terminate)(void* state)) {
        ((SolverWrapper*)solver)->setTermCallback(state, terminate);
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_set_export(void* solver, void* state, int32_t max_length,
            void (*learned)(void* state, int32_t const* clause)) {
        ((SolverWrapper*)solver)->setLearnCallback(state, max_length, learned);
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_set_import(void* solver, void* data, ipasir2_redundancy pledge,
            void (*import)(void* data, ipasir2_redundancy min)) {
        return IPASIR2_E_UNSUPPORTED;
    }

    ipasir2_errorcode ipasir2_set_notify(void* solver, void* data, 
            void (*notify)(void* data, int32_t const* assigned, int32_t const* unassigned)) {
        return IPASIR2_E_UNSUPPORTED;
    }
};
