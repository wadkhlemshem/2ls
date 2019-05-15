/*******************************************************************\

Module: Strategy solver for disjunctive domains

Author: Johanan Wahlang

\*******************************************************************/

#include "strategy_solver_disjunctive.h"

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
  if (e.disjunct==0)
  {
    // no more unresolved edges
    return improved;
  }

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

    solver<<disjunctive_domain.get_disjunct_constraint(d,value[d]);
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
  
  return disjunctive_domaint::unresolved_edget(0,symbolic_patht());
}
