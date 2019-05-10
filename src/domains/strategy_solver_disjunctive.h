/*******************************************************************\

Module: Strategy solver for disjunctive domains

Author: Johanan Wahlang

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_DISJUNCTIVE_DOMAIN_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_DISJUNCTIVE_DOMAIN_H

#include <ssa/local_ssa.h>
#include "strategy_solver_base.h"
#include "disjunctive_domain.h"

class strategy_solver_disjunctivet:public strategy_solver_baset
{
public:
  strategy_solver_disjunctivet(
    disjunctive_domaint &_disjunctive_domain,
    incremental_solvert &_solver,
    local_SSAt &_SSA,
    const namespacet &_ns):
    strategy_solver_baset(_solver, _ns),
    disjunctive_domain(_disjunctive_domain),
    SSA(_SSA)
  {
  }

  virtual bool iterate(invariantt &inv);

protected:
  disjunctive_domaint &disjunctive_domain;
  local_SSAt &SSA;
};

#endif //CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_DISJUNCTIVE_DOMAIN_H