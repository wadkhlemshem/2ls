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
  class loopt
  {
  public:
    loopt():
      body_nodes()
    {
    }
    local_SSAt::nodest body_nodes;
    std::vector<irep_idt> loophead_objects;
    std::vector<irep_idt>::iterator find_loophead_object(const irep_idt &id);
    void add_loophead_objects(exprt expr);
  };

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
    template_generator(_template_generator),
    current_count(0)
  {
    enumerate_all_paths(template_generator.guards);

    assert(template_generator.loop_present);

    loop=new loopt();
    assert(find_loop(template_generator.loophead_loc,loop));

    loop_copies=new local_SSAt::nodest();
    loopheads=new local_SSAt::nodest();
  }

  virtual bool iterate(invariantt &inv);


protected:
  disjunctive_domaint &disjunctive_domain;
  local_SSAt &SSA;
  template_generator_baset &template_generator;
  std::vector<symbolic_patht> all_paths;
  local_SSAt::nodest *loop_copies;
  local_SSAt::nodest *loopheads;
  loopt *loop;
  unsigned int current_count;

  void enumerate_all_paths(guardst &guards);
  void add_new_replication(
    disjunctive_domaint::disjunctive_valuet &inv,
    const disjunctive_domaint::disjunctt d,
    const invariantt &value);
  disjunctive_domaint::unresolved_edget get_unresolved_edge(
    const disjunctive_domaint::disjunctive_valuet &value);
  void get_post(
    const symbolic_patht &p,
    const disjunctive_domaint::disjunctive_valuet &pre_inv,
    invariantt *post_inv);
  bool find_loop(local_SSAt::locationt &loophead_loc, loopt *loop);
  void rename(exprt &expr, const std::string &suffix, disjunctive_domaint::disjunctt d_src);
  void add_loophead(disjunctive_domaint::disjunctt d);
  void add_edge(
    disjunctive_domaint::disjunctt d_src, 
    symbolic_patht &p,
    disjunctive_domaint::disjunctt d_sink);
};

#endif //CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_DISJUNCTIVE_DOMAIN_H