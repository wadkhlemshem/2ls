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

  struct improvement_rowt
  {
    unsigned disjunct;
    unsigned row;

    improvement_rowt(unsigned _disjunct, unsigned _row):
      disjunct(_disjunct), row(_row)
    {}

    friend bool operator==(
      const improvement_rowt &r1,
      const improvement_rowt &r2)
    {
      return (r1.disjunct==r2.disjunct) && (r1.row==r2.row);
    }
  };

  // struct improve_patht
  // {
  //   std::vector<improve_rowt> path;
  //   bool is_cycle;

  //   improve_patht():
  //     path(), is_cycle(false)
  //   {}
  // };

  // typedef std::vector<improve_patht> improve_pathst;

  typedef std::map<improvement_rowt, std::vector<improvement_rowt>> improvement_grapht;

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
    last_improved(),
    // improve_paths(),
    improve_rows(),
    improvement_graph()
  {
    // enumerate_all_paths(guards);

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
  guardst guards;
  std::vector<symbolic_patht> all_paths;
  local_SSAt::nodest *loop_copies;
  local_SSAt::nodest *loopheads;
  loopt *loop;
  unsigned int current_count;
  replace_mapt renaming_map; // renaming map for new domains
  unsigned sum_bound_counter;
  std::stack<improvement_rowt> last_improved;
  // improve_pathst improve_paths;
  improvement_grapht improvement_graph;
  std::vector<improvement_rowt> improve_rows;

  // handles on values to retrieve from model
  disjunctive_domaint::disjunctive_literalst strategy_post_cond_literals;
  disjunctive_domaint::disjunctive_exprst strategy_post_cond_exprs;
  std::map<unsigned, bvt> strategy_pre_cond_literals;
  std::map<unsigned, exprt::operandst> strategy_pre_cond_exprs;
  disjunctive_domaint::disjunctive_exprst strategy_value_exprs;

  void enumerate_all_paths(guardst &guards);
  void add_new_replication(
    disjunctive_domaint::disjunctive_valuet &inv,
    const disjunctive_domaint::disjunctt d,
    const invariantt &value);
  disjunctive_domaint::unresolved_edget get_unresolved_edge(
    const disjunctive_domaint::disjunctive_valuet &value);
  void get_post(
    const symbolic_patht &p,
    invariantt &pre_inv,
    invariantt &post_inv);
  bool find_loop(local_SSAt::locationt &loophead_loc, loopt *loop);
  void rename(exprt &expr,
    const std::string &src_suffix,
    const std::string &sink_suffix);
  void add_loophead(disjunctive_domaint::disjunctt d);
  void add_edge(
    disjunctive_domaint::disjunctt src, 
    const symbolic_patht &p,
    disjunctive_domaint::disjunctt sink);
  bool iterate_binsearch(disjunctive_domaint::disjunctive_valuet &inv);
  bool find_improvement(disjunctive_domaint::disjunctive_valuet &inv);
  bool find_improving_row(
    const improvement_rowt &from,
    improvement_rowt &to);
  void improve_row(
    disjunctive_domaint::disjunctive_valuet &inv,
    const strategy_solver_disjunctivet::improvement_rowt &to,
    const constant_exprt &value);
  // void add_to_improve_paths(
  //   const improve_rowt &src,
  //   const improve_rowt &sink);
  // improve_pathst::iterator find_path(const improve_rowt &row);
  void print_model(const exprt &expr);
};

#endif //CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_DISJUNCTIVE_DOMAIN_H