/*******************************************************************\

Module: Strategy solver for disjunctive domains

Author: Johanan Wahlang

\*******************************************************************/

#include "strategy_solver_disjunctive.h"
#include "strategy_solver_enumeration.h"

/*******************************************************************\

Function: strategy_solver_disjunctivet::iterate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool strategy_solver_disjunctivet::iterate(
  strategy_solver_baset::invariantt &_inv)
{
  disjunctive_domaint::disjunctive_valuet &inv=
    static_cast<disjunctive_domaint::disjunctive_valuet &>(_inv);

  bool improved=false;

  disjunctive_domaint::unresolved_edget e=get_unresolved_edge(inv);
  if (e.disjunct==inv.size())
  {
    // no more unresolved edges
    return improved;
  }

  invariantt post=get_post(e,inv);

  return improved;
}

/*******************************************************************\

Function: strategy_solver_disjunctivet::get_unresolved_edge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

disjunctive_domaint::unresolved_edget
strategy_solver_disjunctivet::get_unresolved_edge(
  const disjunctive_domaint::disjunctive_valuet &value)
{
  disjunctive_domaint::unresolved_edget e;
  for (auto it=disjunctive_domain.unresolved_set.begin(); 
       it!=disjunctive_domain.unresolved_set.end();)
  {
    solver.new_context();
    disjunctive_domaint::disjunctt d;
    symbolic_patht p;
    d = it->disjunct;
    p = it->path;

    solver<<disjunctive_domain.get_disjunct_constraint(d,*value[d]);
    solver<<p.get_expr();

    if (solver()==decision_proceduret::D_SATISFIABLE)
    {
      e=*it;
      disjunctive_domain.unresolved_set.erase(it);
    }
    else
    {
      it++;
    }
    solver.pop_context();
    return e;
  }
  // couldn't find a feasible edge
  return disjunctive_domaint::unresolved_edget(value.size(),symbolic_patht());
}

/*******************************************************************\

Function: strategy_solver_disjunctivet::get_post

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

strategy_solver_disjunctivet::invariantt
strategy_solver_disjunctivet::get_post(
  const disjunctive_domaint::unresolved_edget &e,
  disjunctive_domaint::disjunctive_valuet &_inv)
{
  domaint *_domain=disjunctive_domain.base_domain();
  disjunctive_domaint::disjunctt d=e.disjunct;
  symbolic_patht p=e.path;
  strategy_solver_baset::invariantt inv=*_inv[d];
  if (disjunctive_domain.get_template_kind()==disjunctive_domaint::TPOLYHEDRA)
  {
    tpolyhedra_domaint domain=*static_cast<tpolyhedra_domaint *>(_domain);
    domain.restrict_to_sympath(p);
    strategy_solver_enumerationt strategy_solver(
      domain,solver,ns);
    strategy_solver.iterate(inv);
    domain.undo_restriction();
  }
  return inv;
}
