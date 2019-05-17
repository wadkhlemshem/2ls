/*******************************************************************\

Module: Strategy solver for disjunctive domains

Author: Johanan Wahlang

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_DISJUNCTIVE_DOMAIN_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_DISJUNCTIVE_DOMAIN_H

#include <ssa/local_ssa.h>
#include "strategy_solver_base.h"
#include "disjunctive_domain.h"
#include "template_generator_base.h"

class strategy_solver_disjunctivet:public strategy_solver_baset
{
public:
  typedef std::vector<exprt> guardst;

  strategy_solver_disjunctivet(
    disjunctive_domaint &_disjunctive_domain,
    incremental_solvert &_solver,
    local_SSAt &_SSA,
    const namespacet &_ns,
    template_generator_baset &_template_generator):
    strategy_solver_baset(_solver, _ns),
    disjunctive_domain(_disjunctive_domain),
    SSA(_SSA),
    template_generator(_template_generator)
  {
    enumerate_all_paths(template_generator.guards);
  }

  virtual bool iterate(invariantt &inv);


protected:
  disjunctive_domaint &disjunctive_domain;
  local_SSAt &SSA;
  template_generator_baset &template_generator;
  std::vector<symbolic_patht> all_paths;

  void enumerate_all_paths(guardst &guards);
  disjunctive_domaint::unresolved_edget get_unresolved_edge(
    const disjunctive_domaint::disjunctive_valuet &value);
  void get_post(
    const symbolic_patht &p,
    const disjunctive_domaint::disjunctive_valuet &pre_inv,
    invariantt *post_inv);
};

#endif //CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_DISJUNCTIVE_DOMAIN_H