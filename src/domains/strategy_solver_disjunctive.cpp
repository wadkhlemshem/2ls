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

  if (disjunctive_domain.template_kind==disjunctive_domaint::TPOLYHEDRA)
  {
    tpolyhedra_domaint *domain=static_cast<tpolyhedra_domaint *>(disjunctive_domain.base_domain());

    // initial strategy
    if (inv.size()==0)
    {
      tpolyhedra_domaint::templ_valuet result;
      domain->initialize(result);
      strategy_solver_enumerationt strategy_solver(
        *domain,solver,ns);
      strategy_solver.iterate(result);
      add_new_replication(inv,0,result);
    }

    disjunctive_domaint::unresolved_edget e=get_unresolved_edge(inv);
    if (e.disjunct==inv.size())
    {
      // no more unresolved edges
      return improved;
    }

    improved=true; // found an unresolved edge

    disjunctive_domaint::disjunctt src=e.disjunct;
    disjunctive_domaint::disjunctt sink;
    symbolic_patht path=e.path;

    tpolyhedra_domaint::templ_valuet *post=
      new tpolyhedra_domaint::templ_valuet(
        *static_cast<tpolyhedra_domaint::templ_valuet *>(inv[src]));
    
    get_post(path,inv,post);

    sink=disjunctive_domain.merge_heuristic(inv, *post);

    if (sink==inv.size())
    {
      add_new_replication(inv,sink,*post);
    }
    else
    {
      domain->join(*inv[sink],*post); // join value
    }
    add_edge(src,path,sink);
  }
  else
  {
    // TODO: implement disjuntive strategy solver for other base domains
    assert(false);
  }
  
  return improved;
}

/*******************************************************************\

Function: strategy_solver_disjunctivet::add_new_replication

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void strategy_solver_disjunctivet::add_new_replication(
  disjunctive_domaint::disjunctive_valuet &inv,
  const disjunctive_domaint::disjunctt d,
  const invariantt &value)
{
  if (disjunctive_domain.template_kind==disjunctive_domaint::TPOLYHEDRA)
  {
    inv.push_back(
      new tpolyhedra_domaint::templ_valuet(
        static_cast<const tpolyhedra_domaint::templ_valuet &>(value)));

    add_loophead(d); // SSA loophead for new disjunct
    
    for (auto path : all_paths)
    {
      disjunctive_domaint::unresolved_edget e(d,path);
      disjunctive_domain.unresolved_set.push_back(e);
    }
  }
  else
  {
    assert(false);
  }
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
    debug() << "-------------------------------------------------" << eom << eom;
    strategy_solver.iterate(*post_inv);
    domain.output_value(debug(),*post_inv,ns);
    debug() << "--------------------------------------------------" << eom << eom;
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

/*******************************************************************\

Function: strategy_solver_disjunctivet::find_loop

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool strategy_solver_disjunctivet::find_loop(
  local_SSAt::locationt &loophead_loc, loopt *loop)
{
  local_SSAt::nodest::iterator n_it=SSA.find_node(loophead_loc);
  if (n_it==SSA.nodes.end())
    return false;
  loop->body_nodes.push_back(*n_it);
  auto &node=loop->body_nodes.back();
  for (local_SSAt::nodet::equalitiest::iterator eq_it=node.equalities.begin();
    eq_it!=node.equalities.end();eq_it++)
  {
    std::string id=id2string(eq_it->lhs().get(ID_identifier));
    if (id.find("phi")!=id.npos)
    {
      eq_it->rhs()=eq_it->rhs().op1(); // remove loop select & init
    }
    loop->add_loophead_objects(*eq_it);
  }

  for (n_it++;n_it->loophead->location!=loophead_loc;n_it++)
  {
    loop->body_nodes.push_back(*n_it);
  }

  return true;
}

/*******************************************************************\

Function: strategy_solver_disjunctivet::loopt::add_loophead_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void strategy_solver_disjunctivet::loopt::add_loophead_objects(exprt expr)
{
  if(expr.id()==ID_symbol ||
     expr.id()==ID_nondet_symbol)
  {
    irep_idt id=expr.get(ID_identifier);
    if (find_loophead_object(id)==loophead_objects.end())
      loophead_objects.push_back(id);
  }
  Forall_operands(it, expr)
    add_loophead_objects(*it);
}

/*******************************************************************\

Function: strategy_solver_disjunctivet::loopt::find_loophead_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::vector<irep_idt>::iterator
  strategy_solver_disjunctivet::loopt::find_loophead_object(
    const irep_idt &id)
{
  std::vector<irep_idt>::iterator it=loophead_objects.begin();
  for (;it!=loophead_objects.end();it++)
  {
    if (*it==id)
      break;
  }
  return it;
}

/*******************************************************************\

Function: strategy_solver_disjunctivet::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void strategy_solver_disjunctivet::rename(
  exprt &expr,
  const std::string &src_suffix="",
  const std::string &sink_suffix="")
{
  if(expr.id()==ID_symbol ||
     expr.id()==ID_nondet_symbol)
  {
    irep_idt id=expr.get(ID_identifier);
    if (loop->find_loophead_object(id)!=loop->loophead_objects.end())
    {
      expr.set(ID_identifier,id2string(id)+src_suffix);
    }
    else
    {
      expr.set(ID_identifier,id2string(id)+sink_suffix);
    }
  }
  Forall_operands(it, expr)
    rename(*it,src_suffix,sink_suffix);
}

/*******************************************************************\

Function: strategy_solver_disjunctivet::add_loophead

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void strategy_solver_disjunctivet::add_loophead(
  disjunctive_domaint::disjunctt d)
{
  local_SSAt::nodest::iterator n_it=loop->body_nodes.begin();
  loopheads->push_back(*n_it);
  local_SSAt::nodet &node=loopheads->back();
  for (auto &eq:node.equalities)
  {
    rename(eq,"_"+std::to_string(d),"");
    solver << eq;
  }
}

/*******************************************************************\

Function: strategy_solver_disjunctivet::add_edge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void strategy_solver_disjunctivet::add_edge(
  disjunctive_domaint::disjunctt src, 
  const symbolic_patht &path,
  disjunctive_domaint::disjunctt sink)
{
  debug() << "Adding new SSA nodes" << eom;

  local_SSAt::nodest::iterator n_it=loop->body_nodes.begin();
  std::string sink_suffix="_"+std::to_string(current_count);
  std::string src_suffix="_"+std::to_string(src);
  for (n_it++;n_it!=loop->body_nodes.end();n_it++)
  {
    if (n_it->equalities.empty() &&
        n_it->constraints.empty() &&
        n_it->function_calls.empty())
      continue;
    
    loop_copies->push_back(*n_it);
    auto &node=loop_copies->back();
    for (local_SSAt::nodet::equalitiest::iterator e_it=node.equalities.begin();
          e_it!=node.equalities.end();e_it++)
    {
      rename(*e_it,src_suffix,sink_suffix);
      solver << *e_it;
    }
    for (local_SSAt::nodet::constraintst::iterator c_it=node.constraints.begin();
          c_it!=node.constraints.end();c_it++)
    {
      rename(*c_it,src_suffix,sink_suffix);
      solver << *c_it;
    }
    for (local_SSAt::nodet::function_callst::iterator f_it=node.function_calls.begin();
          f_it!=node.function_calls.end();f_it++)
    {
      rename(*f_it,src_suffix,sink_suffix);
    }
  }

  for (auto &node:*loopheads)
  {
    for (auto &eq:node.equalities)
    {
      debug() << "(E) " << from_expr(eq) << eom;
    }
    debug() << eom;
  }
  
  for (auto &node:*loop_copies)
  {
    for (auto &eq:node.equalities)
    {
      debug() << "(E) " << from_expr(eq) << eom;
    }
    debug() << eom;
  }

  // add new edge to seen set
  disjunctive_domaint::seen_edget new_edge(src,path,sink);
  disjunctive_domain.seen_set.push_back(new_edge);

  // add new template corresponding to new edge
  debug() << "Adding new templates" << eom;
  
  if (disjunctive_domain.template_kind==disjunctive_domaint::TPOLYHEDRA)
  {
    tpolyhedra_domaint *base_domain=static_cast<tpolyhedra_domaint *>(disjunctive_domain.base_domain());
    // replace_mapt new_renaming_map; // renaming map for new domain
    replace_mapt map; // map from base domain exprts to new domain exprts
    for (auto &x:disjunctive_domain.renaming_map)
    {
      exprt pre_var=x.first;
      exprt post_var=x.second;
      renaming_map[pre_var]=post_var; // keep old renaming map for non-LOOP vars
      rename(pre_var,src_suffix,sink_suffix);
      rename(post_var,src_suffix,sink_suffix);
      renaming_map[pre_var]=post_var;
      map[x.first]=pre_var;
    }

    tpolyhedra_domaint *new_domain=new tpolyhedra_domaint(disjunctive_domain.domain_number,renaming_map,ns);

    for (auto &row:base_domain->templ)
    {
      exprt pre_guard=row.pre_guard;
      exprt aux_expr=row.aux_expr;
      exprt post_guard=row.post_guard;
      exprt expr=row.expr;
      if (row.kind==tpolyhedra_domaint::kindt::LOOP)
      {
        if (map.find(row.pre_guard)==map.end())
        {
          rename(pre_guard,src_suffix,sink_suffix);
          map[row.pre_guard]=pre_guard;
        }
        if (map.find(row.aux_expr)==map.end())
        {
          rename(aux_expr,src_suffix,sink_suffix);
          map[row.aux_expr]=aux_expr;
        }
        if (map.find(row.post_guard)==map.end())
        {
          rename(post_guard,src_suffix,sink_suffix);
          map[row.post_guard]=post_guard;
        }
        replace_expr(map,expr);
        pre_guard=map[row.pre_guard];
        post_guard=map[row.post_guard];
        aux_expr=map[row.aux_expr];
      }
      new_domain->add_template_row(expr,pre_guard,post_guard,aux_expr,row.kind);
    }

    // restrict new domain to symbolic path
    symbolic_patht path_;
    for (auto p:path.path_map)
    {
      exprt guard=p.first;
      rename(guard,src_suffix,sink_suffix);
      path_.path_map[guard]=p.second;
    }
    new_domain->restrict_to_sympath(path_);

    // domains are sorted by sink, then source
    disjunctive_domain.templ[sink][src]=new_domain;

    disjunctive_domain.output_domain(debug(),ns);
    debug() << eom;
  }
  else
  {
    assert(false);
  }

  current_count++;
}
