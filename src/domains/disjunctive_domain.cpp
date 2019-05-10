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
