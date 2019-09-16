/*******************************************************************\

Module: Strategy solver for disjunctive domains

Author: Johanan Wahlang

\*******************************************************************/

#include "strategy_solver_disjunctive.h"
#include "strategy_solver_enumeration.h"

#define SUM_BOUND_VAR "sum_bound#"

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

    tpolyhedra_domaint::templ_valuet pre=*static_cast<tpolyhedra_domaint::templ_valuet *>(inv[src]);
    tpolyhedra_domaint::templ_valuet *post=new tpolyhedra_domaint::templ_valuet();
    domain->initialize(*post);
    
    get_post(path,pre,*post);

    sink=disjunctive_domain.merge_heuristic(inv, *post);

    if (sink==inv.size())
    {
      add_new_replication(inv,sink,*post);
    }
    else
    {
      domain->join(*inv[sink],*post); // join value
    }

    add_edge(src,path,sink); // add SSA nodes & new templates

    while (iterate_binsearch(inv)) { }
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
  disjunctive_domain.templ[d]; // insert empty map of templates
  if (disjunctive_domain.template_kind==disjunctive_domaint::TPOLYHEDRA)
  {
    inv.push_back(
      new tpolyhedra_domaint::templ_valuet(
        static_cast<const tpolyhedra_domaint::templ_valuet &>(value)));

    add_loophead(d); // SSA loophead for new disjunct
    
    // for (auto path : all_paths)
    // {
    //   disjunctive_domaint::unresolved_edget e(d,path);
    //   disjunctive_domain.unresolved_set.push_back(e);
    // }
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
  // for (auto it=disjunctive_domain.unresolved_set.begin(); 
  //      it!=disjunctive_domain.unresolved_set.end();)
  // {
  //   solver.new_context();
  //   disjunctive_domaint::disjunctt d=it->disjunct;
  //   symbolic_patht p=it->path;

  //   if (disjunctive_domain.template_kind==disjunctive_domaint::TPOLYHEDRA)
  //   {
  //     tpolyhedra_domaint *domain=static_cast<tpolyhedra_domaint *>(disjunctive_domain.base_domain());
  //     tpolyhedra_domaint::templ_valuet *v=static_cast<tpolyhedra_domaint::templ_valuet *>(value[d]);
  //     debug() << "Disjunct pre-constraint: " << eom;
  //     debug() << from_expr(domain->to_pre_constraints(*v)) << eom << eom;
  //     solver << domain->to_pre_constraints(*v);
  //     if (solver()==decision_proceduret::D_SATISFIABLE)
  //     {
  //       debug() << "model: " << eom;
  //       for (auto &guard:guards)
  //       {
  //         debug() << from_expr(guard) << " " << from_expr(solver.get(guard)) << eom;
  //       }
  //     }
  //   }
  //   debug() << "Path: " << from_expr(p.get_expr()) << eom;
  //   solver<<p.get_expr();

  //   if (solver()==decision_proceduret::D_SATISFIABLE)
  //   {
  //     debug() << "Path is feasible" << eom << eom;      
  //     e=*it;
  //     it=disjunctive_domain.unresolved_set.erase(it);
  //     solver.pop_context();
  //     if (disjunctive_domain.seen_set.find(e.disjunct)==disjunctive_domain.seen_set.end())
  //     {
  //       std::vector<symbolic_patht> v;
  //       v.push_back(e.path);
  //       std::pair<unsigned int,std::vector<symbolic_patht>> p(e.disjunct,v);
        
  //       disjunctive_domain.seen_set.insert(p);
  //     }
  //     else
  //     {
  //       disjunctive_domain.seen_set[e.disjunct].push_back(e.path);
  //     }
      
  //     break;
  //   }
  //   else
  //   {
  //     debug() << "Path is infeasible" << eom << eom;
  //     it++;
  //     solver.pop_context();
  //   }
  // }

  if (disjunctive_domain.template_kind==disjunctive_domaint::TPOLYHEDRA)
  {
    tpolyhedra_domaint *domain=static_cast<tpolyhedra_domaint *>(disjunctive_domain.base_domain());
    for (disjunctive_domaint::disjunctt d=0; d<value.size(); d++)
    {
      solver.new_context();
      tpolyhedra_domaint::templ_valuet *v=static_cast<tpolyhedra_domaint::templ_valuet *>(value[d]);
      // set pre guard to true
      solver << domain->templ.begin()->pre_guard.op1();
      // set loop exit condition to false
      solver << not_exprt(loop->lc);
      debug() << "Disjunct pre-constraint: " << eom;
      debug() << from_expr(domain->to_pre_constraints(*v)) << eom << eom;
      solver << domain->to_pre_constraints(*v);
      
      if (!disjunctive_domain.seen_set[d].empty())
      {
        // negation of seen edges
        exprt::operandst c;
          
        for (auto &x:disjunctive_domain.seen_set[d])
        {
          c.push_back(x.second.get_expr());
        }
        debug() << "Negating seen paths: " << from_expr(not_exprt(disjunction(c))) << eom << eom;
        solver << not_exprt(disjunction(c));
      }

      if (solver()==decision_proceduret::D_SATISFIABLE)
      {
        debug() << "Feasible path:" << eom;
        symbolic_patht p;
        for (const exprt &guard : guards)
        {
          exprt b=solver.get(guard);
          p.path_map[guard] = b.is_true();
          if (b.is_true())
            debug() << from_expr(guard);
          else
            debug() << from_expr(not_exprt(guard));
          debug() << "&&";
        }
        debug() << "\b\b" << eom << eom;

        e.disjunct=d;
        e.path=p;
        solver.pop_context();
        break;
      }
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
  invariantt &_pre_inv,
  invariantt &_post_inv)
{
  debug() << "Computing post" << eom;
  domaint *_domain=disjunctive_domain.base_domain();
  debug() << "--------------------------------------------------" << eom;
  if (disjunctive_domain.get_template_kind()==disjunctive_domaint::TPOLYHEDRA)
  {
    tpolyhedra_domaint domain(*static_cast<tpolyhedra_domaint *>(_domain));
    tpolyhedra_domaint::templ_valuet &pre_inv=
      static_cast<tpolyhedra_domaint::templ_valuet &>(_pre_inv);
    tpolyhedra_domaint::templ_valuet &post_inv=
      static_cast<tpolyhedra_domaint::templ_valuet &>(_post_inv);
    domain.restrict_to_sympath(p);


    domain.output_value(debug(),post_inv,ns);
    debug() << "-------------------------------------------------" << eom << eom;
    // strategy solver enumeration
    solver.new_context();

    std::cout << "Setting the loop select guard to true" << std::endl;
    // std::cout << "pre guard: " << from_expr(domain.templ.begin()->pre_guard.op1()) << std::endl;
    solver << domain.templ.begin()->pre_guard.op1();

    exprt preinv_expr=domain.to_pre_constraints(pre_inv);
  #ifdef DEBUG_OUTPUT
    debug() << "pre-inv: " << from_expr(ns, "", preinv_expr) << eom;
  #endif

    solver << preinv_expr;

    exprt::operandst cond_exprs;
    exprt::operandst value_exprs;
    bvt cond_literals;
    domain.make_not_post_constraints(
      post_inv, cond_exprs, value_exprs);

    cond_literals.resize(cond_exprs.size());

    // exprt postinv_expr=disjunction(cond_exprs);

  #ifdef DEBUG_OUTPUT
    debug() << "post-inv: ";
  #endif
    for(std::size_t i=0; i<cond_exprs.size(); ++i)
    {
  #ifdef DEBUG_OUTPUT
      debug() << (i>0 ? " || " : "") << from_expr(ns, "", cond_exprs[i]);
  #endif

      cond_literals[i]=solver.convert(cond_exprs[i]);
      cond_exprs[i]=literal_exprt(cond_literals[i]);
    }
  #ifdef DEBUG_OUTPUT
    debug() << eom;
  #endif

    solver << disjunction(cond_exprs);

  #ifdef DEBUG_OUTPUT
    debug() << "solve(): ";
  #endif

    if(solver()==decision_proceduret::D_SATISFIABLE)
    {
  #ifdef DEBUG_OUTPUT
      debug() << "SAT" << eom;
  #endif

  #ifdef DEBUG_OUTPUT
      for(std::size_t i=0; i<solver.activation_literals.size(); ++i)
      {
        debug() << "literal: " << solver.activation_literals[i] << " "
                << solver.l_get(solver.activation_literals[i]) << eom;
      }
      for(std::size_t i=0; i<solver.formula.size(); ++i)
      {
        debug() << "literal: " << solver.formula[i] << " "
                << solver.l_get(solver.formula[i]) << eom;
      }
      for(std::size_t i=0; i<tpolyhedra_domain.template_size(); ++i)
      {
        exprt c=tpolyhedra_domain.get_row_constraint(i, inv[i]);
        debug() << "cond: " << from_expr(ns, "", c) << " "
                << from_expr(ns, "", solver.get(c)) << eom;
        debug() << "guards: "
                << from_expr(ns, "", tpolyhedra_domain.templ[i].pre_guard)
                << " " << from_expr(
                  ns, "", solver.get(tpolyhedra_domain.templ[i].pre_guard))
                << eom;
        debug() << "guards: "
                << from_expr(ns, "", tpolyhedra_domain.templ[i].post_guard) << " "
                << from_expr(
                  ns, "", solver.get(tpolyhedra_domain.templ[i].post_guard))
                << eom;
      }

      {
        std::set<symbol_exprt> vars;
        find_symbols(preinv_expr, vars);

        for(const auto &var : vars)
        {
          debug() << "var: " << from_expr(ns, "", var) << "="
                  << from_expr(ns, "", solver.get(var)) << eom;
        }
      }
      for(std::size_t i=0; i<tpolyhedra_domain.template_size(); ++i)
      {
        std::set<symbol_exprt> vars;
        find_symbols(strategy_value_exprs[i], vars);

        for(const auto &var : vars)
        {
          debug() << "var: " << from_expr(ns, "", var) << "="
                  << from_expr(ns, "", solver.get(var)) << eom;
        }
      }
  #endif

      for(std::size_t row=0; row<cond_literals.size(); ++row)
      {
        if(solver.l_get(cond_literals[row]).is_true())
        {
          debug() << "updating row: " << row << eom;

          exprt value=solver.get(value_exprs[row]);
          tpolyhedra_domaint::row_valuet v=simplify_const(value);

          debug() << "raw value; " << from_expr(ns, "", value)
                  << ", simplified value: " << from_expr(ns, "", v) << eom;

          domain.set_row_value(row, v, post_inv);
        }
      }
    }
    else
    {
  #ifdef DEBUG_OUTPUT
      debug() << "UNSAT" << eom;
  #endif

  #ifdef DEBUG_OUTPUT
      for(std::size_t i=0; i<solver.formula.size(); ++i)
      {
        if(solver.solver->is_in_conflict(solver.formula[i]))
          debug() << "is_in_conflict: " << solver.formula[i] << eom;
        else
          debug() << "not_in_conflict: " << solver.formula[i] << eom;
      }
  #endif
    }
    solver.pop_context();


    // strategy_solver_enumerationt strategy_solver(
    //   domain,solver,ns);
    // strategy_solver.iterate(post_inv);


    domain.output_value(debug(),post_inv,ns);
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
    // std::cout << "lhs: " << id2string(id) << std::endl;
    if (id.find("cond")!=id.npos)
    {
      loop->lc=eq_it->lhs();
      // std::cout << "lc: " << from_expr(loop->lc) << std::endl;
    }
    // if (id.find("phi")!=id.npos)
    // {
    //   eq_it->rhs()=eq_it->rhs().op1(); // remove loop select & init
    // }
    loop->add_loophead_objects(*eq_it);
  }

  while (n_it->loophead->location==loophead_loc)
  {
    n_it++;
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
      expr.set(ID_identifier,id2string(id)+src_suffix+sink_suffix);
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
  debug() << "Adding new loophead" << eom;
  local_SSAt::nodest::iterator n_it=loop->body_nodes.begin();
  loopheads->push_back(*n_it);
  local_SSAt::nodet &node=loopheads->back();
  for (const equal_exprt &eq:node.equalities)
  {
    equal_exprt eq_(eq);
    rename(eq_,"_"+std::to_string(d),"");
    solver << eq_;
    const exprt &rhs=eq.rhs();
    if (rhs.id()==ID_symbol)
    {
      debug() << "rhs: " << id2string(rhs.get(ID_identifier)) << eom;
      auto id=id2string(rhs.get(ID_identifier));
      if (id.find("guard")!=id.npos)
      {
        exprt e=equal_exprt(eq_.rhs(),rhs);
        debug() << "(E) " << from_expr(e) << eom;
        solver << e;
      }
    }
    debug() << "(E) " << from_expr(eq_) << eom;
  }
  debug() << eom;
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
  debug() << "loophead objects: " << eom;
  for (const irep_idt &id:loop->loophead_objects)
  {
    debug() << id2string(id) << " ";
  }
  debug() << eom;
  debug() << "Adding new SSA nodes" << eom;

  local_SSAt::nodest::iterator n_it=loop->body_nodes.begin();
  std::string sink_suffix="_"+std::to_string(sink);
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
      debug() << "(E) " << from_expr(*e_it) << eom;
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
  debug() << eom;

  // for (auto &node:*loopheads)
  // {
  //   for (auto &eq:node.equalities)
  //   {
  //     debug() << "(E) " << from_expr(eq) << eom;
  //   }
  //   debug() << eom;
  // }
  
  // for (auto &node:*loop_copies)
  // {
  //   for (auto &eq:node.equalities)
  //   {
  //     debug() << "(E) " << from_expr(eq) << eom;
  //   }
  //   debug() << eom;
  // }

  // add new edge to seen set
  // disjunctive_domaint::seen_edget new_edge(src,path,sink);
  // disjunctive_domain.seen_set.push_back(new_edge);
  disjunctive_domain.seen_set[src][sink]=path;

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
      solver << pre_guard.op1(); // set loop select guard to TRUE
    }

    // restrict new domain to symbolic path
    symbolic_patht path_;
    for (auto p:path.path_map)
    {
      exprt guard=p.first;
      rename(guard,src_suffix,sink_suffix);
      path_.path_map[guard]=p.second;
    }
    // debug() << "path for new domain: " << from_expr(path_.get_expr()) << eom;
    // new_domain->output_domain(debug(), ns);
    // debug() << eom;
    new_domain->restrict_to_sympath(path_);

    // domains are sorted by source, then sink
    disjunctive_domain.templ[src][sink]=new_domain;

    disjunctive_domain.output_domain(debug(),ns);
    debug() << eom;
  }
  else
  {
    assert(false);
  }

  current_count++;
}

/*******************************************************************\

Function: strategy_solver_disjunctivet::iterate_binsearch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool strategy_solver_disjunctivet::iterate_binsearch(
  disjunctive_domaint::disjunctive_valuet &inv)
{
  assert(disjunctive_domain.get_template_kind()==disjunctive_domaint::TPOLYHEDRA);
  // tpolyhedra_domaint::templ_valuet &inv=
  //   static_cast<tpolyhedra_domaint::templ_valuet &>(_inv);

  bool improved=false;

  solver.new_context(); // for improvement check

  std::map<unsigned,
    std::map<unsigned,
      tpolyhedra_domaint *>> tpolyhedra_domains;

  std::map<unsigned, tpolyhedra_domaint::templ_valuet *> tpolyhedra_values;
  std::map<unsigned, std::map<unsigned, symbol_exprt>> symb_values;

  // consider generating pre-invariants in this loop
  for (unsigned d=0; d<inv.size(); d++)
  {
    // auto &temp=*(inv[d]);
    tpolyhedra_values[d]=static_cast<tpolyhedra_domaint::templ_valuet *>(inv[d]);
    for (std::size_t row=0; row<tpolyhedra_values[d]->size(); row++)
    {
      symb_values[d][row]=symbol_exprt(
        "symb_bound#"+i2string(disjunctive_domain.domain_number)+"_"+i2string(d)+"$"+i2string(row), 
        static_cast<tpolyhedra_domaint *>(disjunctive_domain.base_domain())->templ[row].expr.type());
    }
  }

//   exprt inv_expr=disjunctive_domain.to_pre_constraints(inv);

  // disjunctive_domain.make_not_post_constraints(
  //   inv, disjunctive_strategy_cond_exprs, disjunctive_strategy_value_exprs);

#if 1
  debug() << "improvement check: " << eom;
  debug() << "pre-inv: ";
  bool print_flag=false;
#endif

  for (unsigned src=0; src<inv.size(); src++)
  {
    // unsigned src=src_it.first;
    // for (auto &sink_it:src_it.second)
    if (!disjunctive_domain.templ[src].empty())
    {
      exprt::operandst pre_cond_exprs;
      tpolyhedra_domaint *domain=static_cast<tpolyhedra_domaint *>(disjunctive_domain.templ[src].begin()->second);
      tpolyhedra_domaint::templatet templ=domain->templ;
      const tpolyhedra_domaint::templ_valuet &value=*tpolyhedra_values[src];
      assert(value.size()==templ.size());
      strategy_pre_cond_exprs[src].resize(templ.size());
      for (std::size_t row=0; row<templ.size(); ++row)
      {
        strategy_pre_cond_exprs[src][row]=
          domain->get_row_pre_constraint(row,value[row]);
        strategy_pre_cond_literals[src][row]=
          solver.convert(strategy_pre_cond_exprs[src][row]);
        solver << strategy_pre_cond_exprs[src][row];

#if 1
        debug() << (print_flag ? " && " : "") << from_expr(ns, "", strategy_pre_cond_exprs[src][row]);
        print_flag = true;
#endif
      }
#if 1
      debug() << eom;
#endif
    }
  }

#if 1
  debug() << "post-inv: ";
  print_flag=false;
#endif

  exprt::operandst c;
  for (auto &src_it:disjunctive_domain.templ)
  {
    unsigned src=src_it.first;
    for (auto &sink_it:src_it.second)
    {
      unsigned sink=sink_it.first;

      // exprt::operandst post_cond_exprs;
      // exprt::operandst value_exprs;
      tpolyhedra_domaint *domain=static_cast<tpolyhedra_domaint *>(sink_it.second);
      tpolyhedra_domains[src][sink]=domain;
      tpolyhedra_domaint::templatet templ=tpolyhedra_domains[src][sink]->templ;
      const tpolyhedra_domaint::templ_valuet &value=*tpolyhedra_values[sink];

      assert(value.size()==templ.size());
      strategy_post_cond_exprs[src][sink].resize(templ.size());
      strategy_value_exprs[src][sink].resize(templ.size());
      strategy_post_cond_literals[src][sink].resize(templ.size());

      for (std::size_t row=0; row<templ.size(); ++row)
      {
        strategy_value_exprs[src][sink][row]=templ[row].expr;
        domain->rename(strategy_value_exprs[src][sink][row]);
        
        strategy_post_cond_exprs[src][sink][row]=
          and_exprt(templ[row].aux_expr,
            not_exprt(domain->get_row_post_constraint(row, value[row])));

#if 1
        debug() << (print_flag ? " || " : "") << from_expr(ns, "", strategy_post_cond_exprs[src][sink][row]);
        print_flag=true;
#endif 

        literalt &l=strategy_post_cond_literals[src][sink][row];
        strategy_post_cond_literals[src][sink][row]=
          solver.convert(strategy_post_cond_exprs[src][sink][row]);
        strategy_post_cond_exprs[src][sink][row]=
          literal_exprt(l);
        c.push_back(strategy_post_cond_exprs[src][sink][row]);
      }
#if 1
      debug() << eom;
#endif
    }
  }

  solver << disjunction(c);
#if 1
  debug() << eom;
#endif

  std::map<unsigned,
    std::map<tpolyhedra_domaint::rowt, 
      constant_exprt>> lower_values;
  // exprt::operandst blocking_constraint;

#if 1
  debug() << "solve(): ";
#endif

  while (solver()==decision_proceduret::D_SATISFIABLE)
  {
#if 1
    debug() << "SAT" << eom;
#endif
    while(find_improvement(inv))
    {

    }
  }
}

void strategy_solver_disjunctivet::print_model(const exprt &expr)
{
  forall_operands(it, expr)
  {
    if(it->id()==ID_symbol)
    {
      debug() << from_expr(*it) << ": "
        << from_expr(simplify_const(solver.get(*it))) << eom;
    }
    else
    {
      print_model(*it);
    }    
  }
}

bool strategy_solver_disjunctivet::find_improvement(
  disjunctive_domaint::disjunctive_valuet &inv)
{
  while (!last_improved.empty())
  {
    const improvement_rowt &from=last_improved.top();
    unsigned src=from.disjunct;
    improvement_rowt to(from);

    if (find_improving_row(from,to))
    {
      debug() << eom;
      unsigned sink=to.disjunct;
      unsigned row=to.row;
      const constant_exprt &value=simplify_const(solver.get(strategy_value_exprs[src][sink][row]));
      improve_row(inv,to,value);
      // improvement_graph[from].push_back(to);
      return true;
    }
    last_improved.pop();
  }

  for (const auto &src_it : strategy_post_cond_literals)
  {
    unsigned src=src_it.first;

    for (const auto &sink_it : src_it.second)
    {
      unsigned sink=sink_it.first;
      const bvt &cond_literals=sink_it.second;
      for (unsigned i=0; i<cond_literals.size(); i++)
      {
        if (solver.l_get(cond_literals[i]).is_true())
        {
          improvement_rowt to(sink,i);
          const constant_exprt &value=simplify_const(solver.get(strategy_value_exprs[src][sink][i]));
          improve_row(inv,to,value);
          return true;
        }
      }
    }
  }
  return false;
}

// strategy_solver_disjunctivet::improve_pathst::iterator
//   strategy_solver_disjunctivet::find_path(const improve_rowt &row)
// {
//   improve_pathst::iterator it=improve_paths.begin();
//   for (;it!=improve_paths.end(); it++)
//   {
//     if (!(it->is_cycle) && (it->path.back()==row))
//     {
//       return it;
//     }
//   }
//   return it;
// }

bool strategy_solver_disjunctivet::find_improving_row(
  const strategy_solver_disjunctivet::improvement_rowt &from,
  strategy_solver_disjunctivet::improvement_rowt &to)
{
  solver.new_context();
  unsigned src=from.disjunct;
  solver << strategy_pre_cond_exprs[src][from.row];
  debug() << "isolating improvement from " << from_expr(ns, "", strategy_pre_cond_exprs[src][from.row]) << eom;
  // consider using solver->set_assumptions instead
  
  for (const auto &sink_it : disjunctive_domain.templ[src])
  {
    to.disjunct=sink_it.first;
    unsigned sink=to.disjunct;
    exprt::operandst &post_cond_exprs=strategy_post_cond_exprs[src][sink];
    solver << disjunction(post_cond_exprs);
    if (solver()==decision_proceduret::D_SATISFIABLE)
    {
      for (unsigned row=0; row<post_cond_exprs.size(); row++)
      {
        if (solver.l_get(strategy_post_cond_literals[src][sink][row]).is_true())
        {
          to.row=row;
          solver.pop_context();
          return true;
        }
      }
    }
  }

  solver.pop_context();
  return false;
}

void strategy_solver_disjunctivet::improve_row(
  disjunctive_domaint::disjunctive_valuet &inv,
  const strategy_solver_disjunctivet::improvement_rowt &to,
  const constant_exprt &value)
{
  unsigned sink=to.disjunct;
  unsigned row=to.row;
  tpolyhedra_domaint::templ_valuet *v=static_cast<tpolyhedra_domaint::templ_valuet*>(inv[sink]);

  v->at(row)=value;

  if (!disjunctive_domain.templ[sink].empty())
  {
    tpolyhedra_domaint *domain=static_cast<tpolyhedra_domaint *>(disjunctive_domain.templ[sink].begin()->second);
    tpolyhedra_domaint::templatet &templ=domain->templ;

    strategy_pre_cond_exprs[sink][row]=
      domain->get_row_pre_constraint(row,value);
    strategy_pre_cond_literals[sink][row]=
      solver.convert(strategy_pre_cond_exprs[sink][row]);
  }

  // disable all other edges feeding into irow
  for (unsigned src=0;src<inv.size();src++)
  {
    if (disjunctive_domain.templ[src].find(sink)!=disjunctive_domain.templ[src].end())
    {
      tpolyhedra_domaint *domain=static_cast<tpolyhedra_domaint *>(disjunctive_domain.templ[src][sink]);
      tpolyhedra_domaint::templatet &templ=domain->templ;
      strategy_post_cond_exprs[src][sink][row]=
        and_exprt(templ[row].aux_expr,
          not_exprt(domain->get_row_post_constraint(row, value)));
      strategy_post_cond_literals[src][sink][row]=
        solver.convert(strategy_post_cond_exprs[src][sink][row]);
      strategy_post_cond_exprs[src][sink][row]=
        literal_exprt(strategy_post_cond_literals[src][sink][row]);
      solver << literal_exprt(!(strategy_post_cond_literals[src][sink][row]));
    }
  }
}