/*******************************************************************\

Module: Disjunctive domain

Author: Johanan Wahlang

\*******************************************************************/

#ifdef DEBUG
#include <iostream>
#include <langapi/languages.h>
#endif

#include <util/find_symbols.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>

#include "disjunctive_domain.h"
#include "util.h"
#include "domain.h"

#define SYMB_BOUND_VAR "symb_bound#"

#define ENABLE_HEURISTICS

/*******************************************************************\

Function: disjunctive_domaint::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void disjunctive_domaint::initialize(valuet &value)
{
#if 0
  if(templ.size()==0)
    return domaint::initialize(value);
#endif

  disjunctive_valuet &v=static_cast<disjunctive_valuet &>(value);
  v.resize(templ.size());
  for (auto &d : templ)
  {
    for (auto &t : d.second)
    {
      t.second.initialize(v[d.first]);
    }
  }
}

/*******************************************************************\

Function: tpolyhedra_domaint::join

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void disjunctive_domaint::join(valuet &value1, const valuet &value2)
{
#if 0
  if(templ.size()==0)
    return domaint::join(value1, value2);
#endif

  disjunctive_valuet &v1=static_cast<disjunctive_valuet&>(value1);
  const disjunctive_valuet &v2=static_cast<const disjunctive_valuet&>(value2);
  v1.resize(v1.size() + v2.size());
  for(std::size_t disjunct=v1.size(); disjunct<v1.size()+v2.size(); ++disjunct)
  {
    v1[disjunct]=v2[disjunct];
  }

  //TODO: merge heuristic for interval polyhedral domain
}

/*******************************************************************\

Function: disjunctive_domaint::output_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void disjunctive_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &value,
  const namespacet &ns) const
{
  const disjunctive_valuet &v = static_cast<const disjunctive_valuet &>(value);

  for (auto &d : templ)
  {
    auto t=d.second;
    for (auto &i : t)
    {
      i.second.output_value(out,v[d.first],ns);
    }
  }
}

/*******************************************************************\

Function: disjunctive_domaint::output_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void disjunctive_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  for (auto &d : templ)
  {
    for (auto &i : d.second)
    {
      i.second.output_domain(out,ns);
    }
  }
}

/*******************************************************************\

Function: disjunctive_domaint::project_on_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void disjunctive_domaint::project_on_vars(
  domaint::valuet &value,
  const domaint::var_sett &vars,
  exprt &result)
{
  disjunctive_valuet &v=static_cast<disjunctive_valuet &>(value);

  result = false_exprt();
  exprt disjunct_result;
  for (auto &d : templ)
  {
    d.second.begin()->second.project_on_vars(v[d.first], vars, disjunct_result);
    result = or_exprt(result, disjunct_result);
  }
}

/*******************************************************************\

Function: disjunctive_domaint::merge_heuristic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

disjunctive_domaint::disjunctt disjunctive_domaint::merge_heuristic(disjunctive_valuet &dv, valuet &value)
{
  if (template_kind==TPOLYHEDRA)
  {
    tpolyhedra_domaint::templ_valuet &v_new=static_cast<tpolyhedra_domaint::templ_valuet &>(value);
    ieee_floatt inf;
    inf.make_plus_infinity();
    lex_metrict min_distance(dv.size(),inf);
    disjunctt min_disjunct=0;
    for (disjunctt d=0; d<dv.size(); d++)
    {
      tpolyhedra_domaint::templ_valuet &v=static_cast<tpolyhedra_domaint::templ_valuet &>(dv[d]);
      lex_metrict distance=hausdorff_distance(v, v_new);
      if (distance<min_distance)
      {
        min_distance=distance;
        min_disjunct=d;
      }
    }
    if (dv.size()<max &&
        min_distance>tol)
    {
      return dv.size();
    }
    else
    {
      return min_disjunct;
    }
  }
  else
  {
    //TODO: merge heuristic for other templates
    std::cout << "Merge heuristic template kind not yet implemented" << std::endl;
    assert(false);
  }  
}

/*******************************************************************\

Function: disjunctive_domaint::hausdorff_distance

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

disjunctive_domaint::lex_metrict disjunctive_domaint::hausdorff_distance(
  const tpolyhedra_domaint::templ_valuet &value1,
  const tpolyhedra_domaint::templ_valuet &value2)
{
  assert(value1.size()==value2.size());
  ieee_floatt zero;
  unsigned int incomparable=0;
  ieee_floatt dist=zero;
  for (std::size_t i=0; i<value1.size(); i+=2)
  {
    tpolyhedra_domaint::row_valuet u1=value1[i];
    tpolyhedra_domaint::row_valuet l1=value1[i+1];
    tpolyhedra_domaint::row_valuet u2=value2[i];
    tpolyhedra_domaint::row_valuet l2=value2[i+1];

    if (l1.is_boolean() ||
        u1.is_boolean() ||
        l2.is_boolean() ||
        u2.is_boolean())
    {
      if (l1.is_false() ||
          u1.is_false() ||
          l2.is_false() ||
          u2.is_false())
      {
        continue;
      }
      else if (l1.is_true() &&
               l2.is_true() &&
               u1.is_true() &&
               u2.is_true())
      {
        incomparable++;
      }
      else if (l1.is_true() && u1.is_true()) // (-oo,oo) [,]
      {
        incomparable++;
      }
      else if (l2.is_true() && u2.is_true()) // [,] (-oo,oo)
      {
        incomparable++;
      }
      else if (l1.is_true() && !(l2.is_boolean()))
      {
        incomparable++;
      }
      else if (l2.is_true() && !(l1.is_boolean()))
      {
        incomparable++;
      }
      else if (u1.is_true() && !(u1.is_boolean()))
      {
        incomparable++;
      }
      else if (u2.is_true() && !(u1.is_boolean()))
      {
        incomparable++;
      }
      else if (l1.is_true() && l2.is_true())
      {
        dist+=distance(u1,u2);
      }
      else if (u1.is_true() && u2.is_true())
      {
        dist+=distance(l1,l2);
      }
    }  
    else
    {
      ieee_floatt d1=distance(l1,l2);
      ieee_floatt d2=distance(u1,u2);
      if (d1>d2)
      {
        dist+=d1;
      }
      else
      {
        dist+=d2;
      }      
    }
  }
  return lex_metrict(incomparable,dist);
}

/*******************************************************************\

Function: disjunctive_domaint::distance

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ieee_floatt disjunctive_domaint::distance(const constant_exprt &v1, const constant_exprt &v2)
{
  ieee_floatt diff;
  if(v1.type()==v2.type() &&
     (v1.type().id()==ID_signedbv || v1.type().id()==ID_unsignedbv))
  {
    mp_integer vv1, vv2;
    to_integer(v1, vv1);
    to_integer(v2, vv2);
    diff.from_integer(vv1-vv2);
  }
  else if(v1.type().id()==ID_floatbv && v2.type().id()==ID_floatbv)
  {
    ieee_floatt vv1(to_constant_expr(v1));
    ieee_floatt vv2(to_constant_expr(v2));
    diff=ieee_floatt(vv1);
    diff-=vv2;
  }
  else
  {
    assert(false); // types do not match or are not supported
  }
  diff.set_sign(false);
  return diff;
}