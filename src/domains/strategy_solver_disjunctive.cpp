/*******************************************************************\

Module: Strategy solver for disjunctive domains

Author: Johanan Wahlang

\*******************************************************************/

#include "strategy_solver_disjunctive.h"
#include "strategy_solver_enumeration.h"

#define SUM_BOUND_VAR "sum_bound#"

#define tpolyhedra_value(value) \
  static_cast<tpolyhedra_valuet &>(value)

#define tpolyhedra_domain(domain) \
  static_cast<tpolyhedra_domaint *>(domain)

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
    tpolyhedra_domaint *domain=tpolyhedra_domain(disjunctive_domain.base_domain());

    // initial strategy
    if (inv.size()==0)
    {
      tpolyhedra_valuet pre, post;
      domain->initialize(pre);
      domain->initialize(post);
      replace_mapt map=disjunctive_domain.renaming_map;
      if (disjunctive_domain.std_invariants)
      {
        domain->renaming_map=disjunctive_domain.aux_renaming_map;
      }
      get_post(symbolic_patht(),pre,post,true);

      if (disjunctive_domain.std_invariants)
      {
        domain->renaming_map=map;
      
        for (unsigned row=0; row<domain->templ.size(); row++)
        {
          auto &templ_row=domain->templ[row];
          templ_row.post_guard=templ_row.post_guard.op0();
          templ_row.aux_expr=true_exprt();

          exprt post1=templ_row.expr;
          disjunctive_domain.rename(post1);
          exprt post2=templ_row.expr;
          domain->rename(post2);
          debug() << from_expr(templ_row.expr) << " " << from_expr(post1) << " " << from_expr(post2) << eom;
        }
      }
      debug() << "Initial value: " << eom;
      domain->output_value(debug(),post,ns);
      debug() << eom;
      add_new_replication(inv,0,post);
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
    const symbolic_patht &path=e.path;

    tpolyhedra_valuet &pre=tpolyhedra_value(*inv[src]);
    tpolyhedra_valuet post;
    domain->initialize(post);
    
    get_post(path,pre,post);
    domain->output_value(debug(),post,ns);
    debug() << eom << eom;

    sink=disjunctive_domain.merge_heuristic(inv, post);

    if (sink==inv.size())
    {
      add_new_replication(inv,sink,post);
      for (unsigned row=0;row<post.size();row++)
      {
        last_improved.push(improvementt(improvement_rowt(sink,row), false_exprt()));
      }
    }
    else
    {
      join(inv,sink,post); // join value
    }

    add_edge(src,path,sink); // add SSA nodes & new templates

    strategyt cur_strategy, old_strategy;
    while(find_strategy(inv,cur_strategy))
    {
      for (const auto &[sink, src] : old_strategy)
      {
        if (cur_strategy.find(sink)!=cur_strategy.end())
        {
          cur_strategy[sink]=src;
        }
      }
      compute_fixpoint(inv,cur_strategy);
      old_strategy=cur_strategy;
    }
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
      new tpolyhedra_valuet(static_cast<const tpolyhedra_valuet &>(value)));

    add_loophead(d); // SSA loophead for new disjunct
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
  disjunctive_domaint::disjunctive_valuet &value)
{
  disjunctive_domaint::unresolved_edget e(value.size(),symbolic_patht());

  if (disjunctive_domain.template_kind==disjunctive_domaint::TPOLYHEDRA)
  {
    tpolyhedra_domaint *domain=tpolyhedra_domain(disjunctive_domain.base_domain());
    for (disjunctive_domaint::disjunctt d=0; d<value.size(); d++)
    {
      solver.new_context();
      tpolyhedra_valuet &v=tpolyhedra_value(*value[d]);
      // set pre guard to true
      solver << domain->templ.begin()->pre_guard.op1();
      // set loop exit condition to false
      solver << not_exprt(loop->lc);
      debug() << "Disjunct pre-constraint: " << eom;
      debug() << from_expr(domain->to_pre_constraints(v)) << eom << eom;
      solver << domain->to_pre_constraints(v);
      
      if (!disjunctive_domain.seen_set[d].empty())
      {
        // negation of seen edges
        exprt::operandst c;
          
        for (const auto &[_,path]:disjunctive_domain.seen_set[d])
        {
          c.push_back(disjunction(path));
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
        }
        debug() << from_expr(ns,"",p.get_expr()) << eom << eom;

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
  const symbolic_patht &path,
  invariantt &_pre_inv,
  invariantt &_post_inv,
  bool init)
{
  debug() << "Computing post" << eom;
  if (disjunctive_domain.get_template_kind()==disjunctive_domaint::TPOLYHEDRA)
  {
    tpolyhedra_domaint *domain=tpolyhedra_domain(disjunctive_domain.base_domain());
    const tpolyhedra_valuet &pre_inv=
      tpolyhedra_value(_pre_inv);
    tpolyhedra_valuet &post_inv=
      tpolyhedra_value(_post_inv);
    domain->restrict_to_sympath(path);

    solver.new_context(); // pre constraint

    if (init)
    {
      std::cout << "Setting the loop select guard to false" << std::endl;
      solver << not_exprt(domain->templ.begin()->pre_guard.op1());
    }
    else
    {
      std::cout << "Setting the loop select guard to true" << std::endl;
      solver << domain->templ.begin()->pre_guard.op1();  
    }
    
    exprt preinv_expr=domain->to_pre_constraints(pre_inv);
  #ifdef DEBUG_OUTPUT
    debug() << "pre-inv: " << from_expr(ns, "", preinv_expr) << eom;
  #endif

    solver << preinv_expr;

    solver.new_context(); // post constraint
    exprt::operandst cond_exprs;
    exprt::operandst value_exprs;
    bvt cond_literals;
    domain->make_not_post_constraints(
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

    bool improved=false;
    std::map<unsigned,constant_exprt> lower_values;
    while(solver()==decision_proceduret::D_SATISFIABLE)
    {
      improved=true;
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

      exprt::operandst blocking_constraint;
      for(std::size_t row=0; row<cond_literals.size(); ++row)
      {
        if(solver.l_get(cond_literals[row]).is_true())
        {
          debug() << "updating row: " << row << eom;

          exprt value=solver.get(value_exprs[row]);
          tpolyhedra_domaint::row_valuet v=simplify_const(value);

          debug() << "raw value; " << from_expr(ns, "", value)
                  << ", simplified value: " << from_expr(ns, "", v) << eom;
          lower_values[row]=v;
          blocking_constraint.push_back(literal_exprt(!cond_literals[row]));
        }
      }
      solver << conjunction(blocking_constraint);
    }
    solver.pop_context(); // post constraint
    for (auto &[row, lower] :  lower_values)
    {
      solver.new_context(); // symbolic value system
      auto &templ_row=domain->templ[row];
      symbol_exprt symb_value=domain->get_row_symb_value(row);
      exprt c=and_exprt(templ_row.post_guard,
        binary_relation_exprt(templ_row.expr, ID_ge, symb_value));
      domain->rename(c);
      exprt post=and_exprt(templ_row.aux_expr,c);
      solver << post;
      constant_exprt upper=domain->get_max_row_value(row);
      binsearch(domain, symb_value, lower, upper);
      domain->set_row_value(row,lower,post_inv);
      solver.pop_context(); // symbolic value system
    }
    
    if(!improved)
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
    solver.pop_context(); // pre constraint

    domain->undo_restriction();
  }
  else
  {
    assert(false);
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
    if (id.find("phi")!=id.npos)
    {
      eq_it->rhs()=eq_it->rhs().op1(); // remove loop select & init
    }
    loop->add_loophead_objects(*eq_it);
  }

  while (n_it->loophead->location!=loophead_loc)
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
  // auto node=*n_it;
  loopheads.push_back(*n_it);
  auto &node=loopheads.back();
  for (equal_exprt &eq:node.equalities)
  {
    auto rhs=eq.rhs();
    // equal_exprt eq_(eq);
    rename(eq,"_"+std::to_string(d),"");
    const exprt &rhs_=eq.rhs();
    if (rhs.id()==ID_symbol)
    {
      auto id=id2string(rhs.get(ID_identifier));
      if (id.find("guard")!=id.npos)
      {
        exprt e=equal_exprt(rhs_,rhs);
        debug() << "(E) " << from_expr(e) << eom;
        solver << e;
      }
    }
    debug() << "(E) " << from_expr(eq) << eom;
    solver << eq;
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
  const disjunctive_domaint::disjunctt &src, 
  const symbolic_patht &path,
  const disjunctive_domaint::disjunctt &sink)
{
  // check if edge from same src to same sink exists already
  // if so, merge the paths
  if (disjunctive_domain.seen_set[src].find(sink)
      != disjunctive_domain.seen_set[src].end())
  {
    exprt::operandst &seen=disjunctive_domain.seen_set[src][sink];
    if (disjunctive_domain.template_kind==disjunctive_domaint::TPOLYHEDRA)
    {
      tpolyhedra_domaint *domain=tpolyhedra_domain(disjunctive_domain.templ[src][sink]);
      const exprt c=path.get_expr();
      seen.push_back(c);
      for(auto &row : domain->templ)
      {
        row.aux_expr=disjunction(seen);
      }
    }
    return;
  }

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
  }
  debug() << eom;

  exprt p=path.get_expr();
  disjunctive_domain.seen_set[src][sink].push_back(p);
  rename(p, src_suffix, sink_suffix);

  // add new template corresponding to new edge
  debug() << "Adding new templates" << eom;
  
  if (disjunctive_domain.template_kind==disjunctive_domaint::TPOLYHEDRA)
  {
    tpolyhedra_domaint *base_domain=tpolyhedra_domain(disjunctive_domain.base_domain());
    replace_mapt map; // map from base domain exprts to new domain exprts

    for (const auto &x:disjunctive_domain.renaming_map)
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
        aux_expr=p; // restrict to path
      }
      new_domain->add_template_row(expr,pre_guard.op0(),post_guard,aux_expr,row.kind);
    }

    // domains are sorted by source, then sink
    disjunctive_domain.templ[src][sink]=new_domain;

    disjunctive_domain.output_domain(debug(),ns);
    debug() << eom;
  }
  else
  {
    assert(false);
  }
}

/*******************************************************************\

Function: strategy_solver_disjunctivet::binsearch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void strategy_solver_disjunctivet::compute_fixpoint(
  disjunctive_domaint::disjunctive_valuet &inv,
  strategyt strategy)
{
  assert(disjunctive_domain.get_template_kind()==disjunctive_domaint::TPOLYHEDRA);

  // bool improved=false;

  std::vector<std::vector<improvement_rowt>> cycles;
  auto it=strategy.begin();
  while (it!=strategy.end())
  {
    bool cycle_found=false;
    auto sink=it->first;
    debug() << sink.first << "," << sink.second << eom;
    std::vector<improvement_rowt> cycle;
    cycle.push_back(sink);

    while (strategy.find(sink)!=strategy.end())
    {
      sink=strategy[sink];
      cycle.push_back(sink);
      if (sink==cycle.front())
      {
        it=strategy.erase(it);
        cycle_found=true;
        cycles.push_back(cycle);
        break;
      }
    }
    if (!cycle_found)
      it++;
  }

  if (!cycles.empty())
  {
    debug() << "Cycles found: " << eom;
    for (const auto &cycle : cycles)
    {
      for (const auto &row : cycle)
      {
        strategy.erase(row);
        debug() << "(" << row.first << "," << row.second << ") ";
      }
      debug() << eom;
    }
  }

  for (const auto &cycle : cycles)
  {
    auto it=cycle.begin();
    auto from = *it;
    auto to=*++it;
    unsigned row=from.second;
    debug() << "improving row " << row << " of disjunct " << from.first << eom;
    constant_exprt lower=tpolyhedra_value(*inv[from.first])[row];
    debug() << "lower: " << from_expr(lower) << eom;

    tpolyhedra_domaint *domain=tpolyhedra_domain(disjunctive_domain.templ[from.first][to.first]);

    constant_exprt upper=domain->get_max_row_value(row);
    debug() << "upper: " << from_expr(upper) << eom;

    auto templ_row=domain->templ[row];
    symbol_exprt symb_value=domain->get_row_symb_value(row);
    std::set<unsigned> improve_rows;
    improve_rows.insert(row);
    exprt pre = domain->to_symb_pre_constraints(tpolyhedra_value(*inv[from.first]), improve_rows);
    solver.new_context(); // path composition
    debug() << "aux: " << from_expr(domain->templ[from.second].aux_expr) << eom;
    solver << domain->templ[from.second].aux_expr;

    for (it++;it!=cycle.end();it++)
    {
      exprt::operandst post_vars;
      for (equal_exprt eq : loopheads[from.first].equalities)
      {
        auto id=id2string(eq.lhs().get(ID_identifier));
        if (id.find("phi")!=id.npos)
        {
          post_vars.push_back(renaming_map[eq.rhs()]);
        }
      }
      exprt::operandst pre_vars;
      for (equal_exprt eq : loopheads[to.first].equalities)
      {
        auto id=id2string(eq.lhs().get(ID_identifier));
        if (id.find("phi")!=id.npos)
        {
          pre_vars.push_back(eq.rhs());
        }
      }
      assert(pre_vars.size()==post_vars.size());
      for (unsigned i=0; i<pre_vars.size(); i++)
      {
        debug() << from_expr(equal_exprt(pre_vars[i],post_vars[i])) << eom;
        solver << equal_exprt(pre_vars[i],post_vars[i]);
      }

      from=to;
      to = *it;
      domain=tpolyhedra_domain(disjunctive_domain.templ[from.first][to.first]);
      debug() << "aux: " << from_expr(domain->templ[from.second].aux_expr) << eom;
      solver << domain->templ[from.second].aux_expr;
    }
    
    solver.new_context(); // symbolic value system
    debug() << "pre: " << from_expr(pre) << eom;
    solver << pre;
    debug() << from_expr(not_exprt(equal_exprt(symb_value, templ_row.expr))) << eom;
    solver << not_exprt(equal_exprt(symb_value, templ_row.expr));

    row = to.second;
    templ_row=domain->templ[row];
    exprt post=and_exprt(
      templ_row.post_guard,
      binary_relation_exprt(templ_row.expr, ID_ge, symb_value));
    domain->rename(post);
    debug() << "post: " << from_expr(post) << eom;
    solver << post;
    
    it=cycle.begin();
    from=*it;
    it++;
    to=*it;
    domain = tpolyhedra_domain(disjunctive_domain.templ[from.first][to.first]);
    if (solver() == decision_proceduret::D_SATISFIABLE)
    {
      debug() << "update value: " << from_expr(ns, "", lower) << eom;
      binsearch(domain,symb_value,lower,upper);

      improve_row(inv, from.first, row, lower);
    }
    solver.pop_context(); // symbolic value system

    // plug in current value for propagation
    domain=tpolyhedra_domain(disjunctive_domain.templ[from.first][to.first]);
    pre = domain->to_pre_constraints(tpolyhedra_value(*inv[from.first]));
    debug() << "pre: " << from_expr(pre) << eom;
    solver << pre;
    solver();
    std::vector<constant_exprt> lower_values;
    for (it++;it!=cycle.end();it++)
    {
      from=to;
      to=*it;
      auto templ_row=domain->templ[from.second];
      exprt post_var=templ_row.expr;
      domain->rename(post_var);
      debug() << from_expr(post_var) << " = " << from_expr(simplify_const(solver.get(post_var))) << eom;
      lower_values.push_back(simplify_const(solver.get(post_var)));
      domain=tpolyhedra_domain(disjunctive_domain.templ[from.first][to.first]);
    }

    assert(lower_values.size()==cycle.size()-2);

    debug() << "Propagating new value to cycle nodes" << eom;
    for (unsigned i=0; i<cycle.size()-2;i++)
    {
      from=cycle[i];
      to=cycle[i+1];
      debug() << "improving row " << to.second << " of disjunct " << to.first << eom;
      solver.new_context(); //symbolic value system
      domain=tpolyhedra_domain(disjunctive_domain.templ[from.first][to.first]);
      templ_row=domain->templ[to.second];
      symb_value=domain->get_row_symb_value(to.second);
      post=and_exprt(templ_row.post_guard,
      binary_relation_exprt(templ_row.expr, ID_ge, symb_value));
      domain->rename(post);
      debug() << "post: " << from_expr(post) << eom;
      solver << post;
      debug() << "aux: " << from_expr(templ_row.aux_expr) << eom;
      solver << templ_row.aux_expr;

      lower=lower_values[i];
      debug() << "update value: " << from_expr(ns, "", lower) << eom;

      upper=domain->get_max_row_value(to.second);

      binsearch(domain,symb_value,lower,upper);

      improve_row(inv, to.first, to.second, lower);

      solver.pop_context(); //symbolic value system
    }

    solver.pop_context(); // path composition
  }

  // TODO : check that this section is correct
  // find paths
  std::vector<std::vector<improvement_rowt>> paths;
  for (auto it=strategy.begin();it!=strategy.end();it++)
  {
    auto to=it->first;
    auto from=it->second;
    bool appended=false;
    for (auto &path:paths)
    {
      if (path.back()==from)
      {
        path.push_back(to);
        appended=true;
      }
    }
    std::vector<improvement_rowt> path;
    if (!appended)
    {
      path.push_back(from);
      path.push_back(to);
      while (strategy.find(from)!=strategy.end())
      {
        from=strategy[from];
        path.insert(path.begin(),from);
      }
      paths.push_back(path);
    }
  }

  if (!paths.empty())
  {
    debug() << "Paths found: " << eom;
    for (const auto &path : paths)
    {
      for (const auto &row : path)
      {
        debug() << "(" << row.first << "," << row.second << ")";
      }
      debug() << eom;
    }
  }

  for (const auto &path : paths)
  {
    solver.new_context(); // path compostion
    auto it=path.begin();
    auto from=*it;
    auto to=*++it;
    tpolyhedra_domaint *domain=tpolyhedra_domain(disjunctive_domain.templ[from.first][to.first]);
    while (it!=path.end())
    {
      debug() << "aux: " << from_expr(domain->templ[from.second].aux_expr) << eom;
      solver << domain->templ[from.second].aux_expr;

      exprt::operandst post_vars;
      for (equal_exprt eq : loopheads[from.first].equalities)
      {
        auto id=id2string(eq.lhs().get(ID_identifier));
        if (id.find("phi")!=id.npos)
        {
          post_vars.push_back(renaming_map[eq.rhs()]);
        }
      }
      exprt::operandst pre_vars;
      for (equal_exprt eq : loopheads[to.first].equalities)
      {
        auto id=id2string(eq.lhs().get(ID_identifier));
        if (id.find("phi")!=id.npos)
        {
          pre_vars.push_back(eq.rhs());
        }
      }
      assert(pre_vars.size()==post_vars.size());
      for (unsigned i=0; i<pre_vars.size(); i++)
      {
        debug() << from_expr(equal_exprt(pre_vars[i],post_vars[i])) << eom;
        solver << equal_exprt(pre_vars[i],post_vars[i]);
      }

      from=to;
      to = *++it;
      domain=tpolyhedra_domain(disjunctive_domain.templ[from.first][to.first]);
    }

    it=path.begin();
    from=*it;
    to=*++it;
    domain=tpolyhedra_domain(disjunctive_domain.templ[from.first][to.first]);
    exprt pre = domain->to_pre_constraints(tpolyhedra_value(*inv[from.first]));
    debug() << "pre: " << from_expr(pre) << eom;
    solver << pre;
    solver();
    std::vector<constant_exprt> lower_values;
    while (it!=path.end())
    {
      auto templ_row=domain->templ[to.second];
      exprt post_var=templ_row.expr;
      domain->rename(post_var);
      debug() << from_expr(post_var) << " = " << from_expr(simplify_const(solver.get(post_var))) << eom;
      lower_values.push_back(simplify_const(solver.get(post_var)));
      from=to;
      to=*++it;
      domain=tpolyhedra_domain(disjunctive_domain.templ[from.first][to.first]);
    }

    for (auto &lower : lower_values)
    {
      debug() << from_expr(lower) << eom;
    }
    assert(lower_values.size()==path.size()-1);

    debug() << "Propagating new value to path nodes" << eom;
    for (unsigned i=0; i<path.size()-1;i++)
    {
      from=path[i];
      to=path[i+1];
      debug() << "improving row " << to.second << " of disjunct " << to.first << eom;
      solver.new_context(); //symbolic value system
      domain=tpolyhedra_domain(disjunctive_domain.templ[from.first][to.first]);
      auto templ_row=domain->templ[to.second];
      symbol_exprt symb_value=domain->get_row_symb_value(to.second);
      exprt post=and_exprt(templ_row.post_guard,
      binary_relation_exprt(templ_row.expr, ID_ge, symb_value));
      domain->rename(post);
      debug() << "post: " << from_expr(post) << eom;
      solver << post;
      debug() << "aux: " << from_expr(templ_row.aux_expr) << eom;
      solver << templ_row.aux_expr;

      constant_exprt lower=lower_values[i];
      debug() << "update value: " << from_expr(ns, "", lower) << eom;

      constant_exprt upper=domain->get_max_row_value(to.second);

      binsearch(domain,symb_value,lower,upper);

      improve_row(inv, to.first, to.second, lower);

      solver.pop_context(); //symbolic value system
    }
    solver.pop_context(); // path composition
  }
}

void strategy_solver_disjunctivet::binsearch(
  tpolyhedra_domaint *domain,
  const symbol_exprt &symb_value,
  constant_exprt &lower,
  constant_exprt &upper)
{
  while(domain->less_than(lower, upper))
  {
    tpolyhedra_domaint::row_valuet middle=
      domain->between(lower, upper);
    if(!domain->less_than(lower, middle))
      middle=upper;

    // row_symb_value >= middle
    exprt c=binary_relation_exprt(symb_value, ID_ge, middle);

#if 1
    debug() << "upper: " << from_expr(ns, "", upper) << eom;
    debug() << "middle: " << from_expr(ns, "", middle) << eom;
    debug() << "lower: " << from_expr(ns, "", lower) << eom;
#endif

    solver.new_context(); // binary search iteration

#if 1
    debug() << "constraint: " << from_expr(ns, "", c) << eom;
#endif

    solver << c;

    if(solver()==decision_proceduret::D_SATISFIABLE)
    {
#if 1
      debug() << "SAT" << eom;
#endif

#if 1
      debug() << from_expr(ns, "", symb_value)
              << " " << from_expr(
                ns, "", solver.get(symb_value))
              << eom;
#endif

      lower=simplify_const(
        solver.get(symb_value));
    }
    else
    {
#if 1
      debug() << "UNSAT" << eom;
#endif

#if 1
      for(std::size_t i=0; i<solver.formula.size(); ++i)
      {
        if(solver.solver->is_in_conflict(solver.formula[i]))
          debug() << "is_in_conflict: " << solver.formula[i] << eom;
        else
          debug() << "not_in_conflict: " << solver.formula[i] << eom;
      }
#endif

      if(!domain->less_than(middle, upper))
        middle=lower;
      upper=middle;
    }
    solver.pop_context(); // binary search iteration
  }
}

void strategy_solver_disjunctivet::print_model(const exprt &expr)
{
  // debug() << from_expr(expr) << eom;
  if (expr.id()==ID_symbol)
  {
    debug() << from_expr(expr) << ": " << from_expr(simplify_const(solver.get(expr))) << eom;
  }
  forall_operands(it,expr)
  {
    print_model(*it);
  }
}

void strategy_solver_disjunctivet::print_all()
{
  for (auto &node: loopheads)
  {
    for (auto &eq : node.equalities)
    {
      print_model(eq);
    }
  }
  for (auto &node : *loop_copies)
  {
    for (auto &eq : node.equalities)
    {
      print_model(eq);
    }
  }
}

bool strategy_solver_disjunctivet::find_strategy(
  const disjunctive_domaint::disjunctive_valuet &inv,
  strategyt &strategy)
{
  bool improved=false;
  while (!last_improved.empty())
  {
    const improvementt &from=last_improved.top();
    debug() << from.first.first << " " << from.first.second << eom;

    if (find_improving_row(inv,from,strategy))
    {
      improved=true;
    }
    else
    {
      last_improved.pop();
    }
  }
  return improved;
}

bool strategy_solver_disjunctivet::find_improving_row(
  const disjunctive_domaint::disjunctive_valuet &inv,
  const improvementt &improvement,
  strategyt &strategy)
{
  const improvement_rowt &from=improvement.first;
  unsigned src=from.first;
  unsigned row=from.second;
  if (disjunctive_domain.templ[src].empty())
    return false;

  solver.new_context(); // pre constraint
  tpolyhedra_domaint *domain=tpolyhedra_domain(disjunctive_domain.templ[src].begin()->second);
  const tpolyhedra_valuet &v=tpolyhedra_value(*inv[src]);
  const tpolyhedra_domaint::templatet &templ=domain->templ;
  exprt::operandst c;
  for (unsigned row=0; row<templ.size(); row++)
  {
    if (row==from.second)
    {
      c.push_back(domain->get_row_pre_constraint(row,improvement.second));
    }
    else
    {
      c.push_back(domain->get_row_pre_constraint(row,v[row]));
    }
  }
  exprt pre=conjunction(c);
  solver << pre;
  debug() << "isolating improvement from " << from_expr(ns, "", pre) << eom;
  
  for (const auto &[sink, sink_domain] : disjunctive_domain.templ[src])
  {
    tpolyhedra_domaint *domain=tpolyhedra_domain(sink_domain);
    tpolyhedra_domaint::templatet &templ=domain->templ;
    for (unsigned row=0; row<templ.size(); row++)
    {
      solver.new_context(); // post constraint
      improvement_rowt to(sink,row);
      const constant_exprt &value=tpolyhedra_value(*inv[sink])[row];
      if (strategy.find(to)==strategy.end())  // check if to is already blocked
      {
        exprt post=and_exprt(templ[row].aux_expr,
            not_exprt(domain->get_row_post_constraint(row, value)));

        solver << post;
        debug() << "post: " << from_expr(post) << eom;
        if (solver()==decision_proceduret::D_SATISFIABLE)
        {
          exprt value_expr=templ[row].expr;
          domain->rename(value_expr);
          debug() << from_expr(value_expr) << " " << from_expr(solver.get(value_expr)) << eom;
          const constant_exprt &value=simplify_const(solver.get(value_expr));
          last_improved.push(improvementt(to,value));
          strategy[to]=from;
          solver.pop_context(); // post constraint
          solver.pop_context(); // pre constraint
          return true;
        }
      }
      solver.pop_context(); // post constraint
    }
  }

  solver.pop_context(); // pre constraint
  return false;
}

void strategy_solver_disjunctivet::join(
  disjunctive_domaint::disjunctive_valuet &inv,
  const unsigned disjunct,
  const tpolyhedra_domaint::templ_valuet &value)
{
  tpolyhedra_domaint *domain=tpolyhedra_domain(disjunctive_domain.base_domain());
  tpolyhedra_domaint::templatet &templ=domain->templ;
  for (unsigned row=0;row<templ.size();row++)
  {
    improve_row(inv,disjunct,row,value[row]);
  }
}

bool strategy_solver_disjunctivet::improve_row(
  disjunctive_domaint::disjunctive_valuet &inv,
  const unsigned disjunct,
  const unsigned row,
  const constant_exprt &row_value)
{
  tpolyhedra_valuet &v=tpolyhedra_value(*inv[disjunct]);
  tpolyhedra_domaint *domain=tpolyhedra_domain(disjunctive_domain.base_domain());
  bool improved=false;
  if(domain->is_row_value_inf(v[row]))
  {
    v[row]=true_exprt();
  }
  else if (domain->is_row_value_inf(row_value))
  {
    v[row]=true_exprt();
    improved=true;
  }
  else if(!domain->is_row_value_neginf(row_value))
  {
    if(domain->less_than(v[row], row_value) || 
      domain->is_row_value_neginf(v[row]))
    {
      v[row]=row_value;
      improved=true;
    }
  }
  if (improved)
    last_improved.push(improvementt(improvement_rowt(disjunct,row),row_value));
  return improved;
}
