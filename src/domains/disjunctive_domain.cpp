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

  templ_valuet &v=static_cast<templ_valuet&>(value);
  v.resize(templ.size());
  for (std::size_t disjunct=0; disjunct<v.size(); disjunct++)
  {
    templ[disjunct].initialize(v[disjunct]);
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

  templ_valuet &v1=static_cast<templ_valuet&>(value1);
  const templ_valuet &v2=static_cast<const templ_valuet&>(value2);
  v1.resize(v1.size() + v2.size());
  for(std::size_t disjunct=v1.size(); disjunct<v1.size()+v2.size(); ++disjunct)
  {
    v1[disjunct]=v2[disjunct];
  }

  //TODO: merge heuristic for interval polyhedral domain
}
