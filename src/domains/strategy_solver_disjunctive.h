/*******************************************************************\

Module: Strategy solver for disjunctive domains

Author: Johanan Wahlang

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_DISJUNCTIVE_DOMAIN_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_DISJUNCTIVE_DOMAIN_H

#include <stack>
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
    exprt lc;
    local_SSAt::nodest body_nodes;
    std::vector<irep_idt> loophead_objects;
    std::vector<irep_idt>::iterator find_loophead_object(const irep_idt &id);
    void add_loophead_objects(exprt expr);
  };

  typedef std::vector<exprt> guardst;

  typedef std::pair<unsigned,unsigned> improvement_rowt;

  typedef std::map<improvement_rowt, improvement_rowt> strategyt;

  typedef std::pair<improvement_rowt, constant_exprt> improvementt;

  typedef tpolyhedra_domaint::templ_valuet tpolyhedra_valuet;

  strategy_solver_disjunctivet(
    disjunctive_domaint &_disjunctive_domain,
    incremental_solvert &_solver,
    local_SSAt &_SSA,
    const namespacet &_ns,
    template_generator_baset &_template_generator):
    strategy_solver_baset(_solver, _ns),
    disjunctive_domain(_disjunctive_domain),
    SSA(_SSA),
    guards(template_generator.guards),
    template_generator(_template_generator),
    current_count(0),
    renaming_map(disjunctive_domain.renaming_map),
    loopheads(),
    last_improved()
  {
    assert(template_generator.loop_present);

    loop=new loopt();
    assert(find_loop(template_generator.loophead_loc,loop));

    loop_copies=new local_SSAt::nodest();
  }

  ~strategy_solver_disjunctivet()
  {
    if (loop!=NULL)
    {
      delete loop;
    }
    if (loop_copies!=NULL)
    {
      delete loop_copies;
    }
  }

  virtual bool iterate(invariantt &inv);

protected:
  disjunctive_domaint &disjunctive_domain;
  local_SSAt &SSA;
  template_generator_baset &template_generator;
  guardst guards;
  local_SSAt::nodest *loop_copies;
  std::vector<local_SSAt::nodet> loopheads;
  loopt *loop;
  unsigned int current_count;
  replace_mapt renaming_map; // renaming map for new domains
  unsigned sum_bound_counter;
  std::stack<improvementt> last_improved;

  // handles on values to retrieve from model
  // disjunctive_domaint::disjunctive_literalst strategy_post_cond_literals;
  // disjunctive_domaint::disjunctive_exprst strategy_post_cond_exprs;
  // std::map<unsigned, bvt> strategy_pre_cond_literals;
  // std::map<unsigned, exprt::operandst> strategy_pre_cond_exprs;
  // disjunctive_domaint::disjunctive_exprst strategy_value_exprs;

  void add_new_replication(
    disjunctive_domaint::disjunctive_valuet &inv,
    const disjunctive_domaint::disjunctt d,
    const invariantt &value);
  disjunctive_domaint::unresolved_edget get_unresolved_edge(
    disjunctive_domaint::disjunctive_valuet &value);
  void get_post(
    const symbolic_patht &path,
    invariantt &pre_inv,
    invariantt &post_inv,
    bool init=false);
  bool find_loop(local_SSAt::locationt &loophead_loc, loopt *loop);
  void rename(exprt &expr,
    const std::string &src_suffix,
    const std::string &sink_suffix);
  void add_loophead(disjunctive_domaint::disjunctt d);
  void add_edge(
    const disjunctive_domaint::disjunctt &src, 
    const symbolic_patht &path,
    const disjunctive_domaint::disjunctt &sink);
  void compute_fixpoint(disjunctive_domaint::disjunctive_valuet &inv,
    strategyt strategy);
  bool find_strategy(
    const disjunctive_domaint::disjunctive_valuet &inv,
    strategyt &strategy);
  bool find_improving_row(
    const disjunctive_domaint::disjunctive_valuet &inv,
    const improvementt &improvement,
    strategyt &strategy);
  void improve_edge(
    disjunctive_domaint::disjunctive_valuet &inv,
    const strategy_solver_disjunctivet::improvement_rowt &from,
    const strategy_solver_disjunctivet::improvement_rowt &to);
  void join(
    disjunctive_domaint::disjunctive_valuet &inv,
    const unsigned disjunct,
    const tpolyhedra_valuet &value);
  bool improve_row(
    disjunctive_domaint::disjunctive_valuet &inv,
    const unsigned disjunct,
    const unsigned row,
    const constant_exprt &row_value);

  void binsearch(
    tpolyhedra_domaint *domain, 
    const symbol_exprt &symb_value, 
    constant_exprt &lower, 
    constant_exprt &upper);
  
  void print_all();
  void print_model(const exprt &expr);
};

#endif //CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_DISJUNCTIVE_DOMAIN_H