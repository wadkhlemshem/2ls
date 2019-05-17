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
  // only iterate on loops for now
  assert(template_generator.loop_present);

  disjunctive_domaint::disjunctive_valuet &inv=
    static_cast<disjunctive_domaint::disjunctive_valuet &>(_inv);

  bool improved=false;

  // initial strategy
  if (inv.size()==0)
  {
    if (disjunctive_domain.template_kind==disjunctive_domaint::TPOLYHEDRA)
    {
      auto result=tpolyhedra_domaint::templ_valuet();
      tpolyhedra_domaint *domain=static_cast<tpolyhedra_domaint *>(disjunctive_domain.base_domain());
      domain->initialize(result);
      strategy_solver_enumerationt strategy_solver(
        *domain,solver,ns);
      strategy_solver.iterate(result);
      inv.push_back(new tpolyhedra_domaint::templ_valuet(static_cast<tpolyhedra_domaint::templ_valuet>(result)));
      
      for (auto path : all_paths)
      {
        disjunctive_domaint::unresolved_edget e(0,path);
        disjunctive_domain.unresolved_set.push_back(e);
      }
    }
    else
    {
      assert(false);
    }
  }

  disjunctive_domaint::unresolved_edget e=get_unresolved_edge(inv);
  if (e.disjunct==inv.size())
  {
    // no more unresolved edges
    return improved;
  }

  disjunctive_domaint::disjunctt d_src=e.disjunct;
  disjunctive_domaint::disjunctt d_sink;
  symbolic_patht p=e.path;
  
  invariantt *post=new tpolyhedra_domaint::templ_valuet(*static_cast<tpolyhedra_domaint::templ_valuet *>(inv[d_src]));
  get_post(p,inv, post);

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
  disjunctive_domaint::unresolved_edget e(value.size(),symbolic_patht());
  for (auto it=disjunctive_domain.unresolved_set.begin(); 
       it!=disjunctive_domain.unresolved_set.end();)
  {
    solver.new_context();
    disjunctive_domaint::disjunctt d=it->disjunct;
    symbolic_patht p=it->path;

    if (disjunctive_domain.template_kind==disjunctive_domaint::TPOLYHEDRA)
    {
      tpolyhedra_domaint *domain=static_cast<tpolyhedra_domaint *>(disjunctive_domain.base_domain());
      tpolyhedra_domaint::templ_valuet *v=static_cast<tpolyhedra_domaint::templ_valuet *>(value[d]);
      debug() << "Disjunct pre-constraint: " << eom;
      debug() << from_expr(domain->to_pre_constraints(*v)) << eom << eom;
      solver << domain->to_pre_constraints(*v);
    }
    debug() << "Path: " << from_expr(p.get_expr()) << eom;
    solver<<p.get_expr();

    if (solver()==decision_proceduret::D_SATISFIABLE)
    {
      debug() << "Path is feasible" << eom << eom;      
      e=*it;
      it=disjunctive_domain.unresolved_set.erase(it);
      solver.pop_context();
      break;
    }
    else
    {
      debug() << "Path is infeasible" << eom << eom;
      it++;
      solver.pop_context();
    }
  }
  return e;
}

/*******************************************************************\

Function: strategy_solver_disjunctivet::get_post

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void strategy_solver_disjunctivet::get_post(
  const symbolic_patht &p,
  const disjunctive_domaint::disjunctive_valuet &pre_inv,
  invariantt *post_inv)
{
  debug() << "Computing post" << eom;
  domaint *_domain=disjunctive_domain.base_domain();
  debug() << "--------------------------------------------------" << eom;
  if (disjunctive_domain.get_template_kind()==disjunctive_domaint::TPOLYHEDRA)
  {
    tpolyhedra_domaint domain(*static_cast<tpolyhedra_domaint *>(_domain));
    domain.restrict_to_sympath(p);
    strategy_solver_enumerationt strategy_solver(
      domain,solver,ns);
    domain.output_value(debug(),*post_inv,ns);
    debug() << "-------------------------------------------------" << eom;
    strategy_solver.iterate(*post_inv);
    domain.output_value(debug(),*post_inv,ns);
    debug() << "--------------------------------------------------" << eom;
    domain.undo_restriction();
  }
  else
  {
    assert(false);
  }
}

/*******************************************************************\

Function: strategy_solver_disjunctivet::enumerate_all_paths

  Inputs:

 Outputs:

 Purpose: Enumerate all paths inside the loop

\*******************************************************************/

void strategy_solver_disjunctivet::enumerate_all_paths(guardst &guards)
{
  for (auto &guard : guards)
  {
    if (all_paths.empty())
    {
      symbolic_patht p;
      p.path_map[guard] = true;
      all_paths.push_back(p);
      p.path_map[guard] = false;
      all_paths.push_back(p);
    }
    else
    {
      std::vector<symbolic_patht> new_paths;
      for (auto &path : all_paths)
      {
        symbolic_patht path_(path);
        path.path_map[guard] = true;
        path_.path_map[guard] = false;
        new_paths.push_back(path_);
      }
      for (auto &path : new_paths)
      {
        all_paths.push_back(path);
      }
    }
  }
}