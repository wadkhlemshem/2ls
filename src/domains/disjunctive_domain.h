/*******************************************************************\

Module: Disjunctive domain

Author: Johanan Wahlang

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_DISJUNCTIVE_DOMAIN_H
#define CPROVER_2LS_DOMAINS_DISJUNCTIVE_DOMAIN_H

#include <iostream>
#include <set>

#include <util/std_expr.h>
#include <util/i2string.h>
#include <langapi/language_util.h>
#include <util/replace_expr.h>
#include <util/namespace.h>

#include "domain.h"
#include "tpolyhedra_domain.h"
#include "symbolic_path.h"

class disjunctive_domaint:public domaint
{
public:
  enum template_kindt
  {
    TPOLYHEDRA, HEAP
  };
  typedef unsigned disjunctt;
  typedef std::map<disjunctt, std::map<unsigned int,domaint>> templatet;

  class disjunctive_valuet:public valuet, public std::vector<valuet>
  {
  };

  disjunctive_domaint(
    unsigned int _domain_number,
    replace_mapt &_renaming_map,
    const var_specst &var_specs,
    const namespacet &_ns,
    const template_kindt _template_kind,
    const disjunctt _max):
    domaint(_domain_number, _renaming_map, _ns),
    template_kind(_template_kind),
    max(_max),
    templ()
  {
    if(template_kind==TPOLYHEDRA)
    {
      base_domain_ptr=new tpolyhedra_domaint(domain_number, renaming_map, ns);
    }
  }

  virtual ~disjunctive_domaint()
  {
    if (base_domain_ptr!=NULL)
      delete base_domain_ptr;
  }

  virtual void initialize(valuet &value);
  
  virtual void join(valuet &value1, const valuet &value2);

  // printing
  virtual void output_value(
    std::ostream &out,
    const valuet &value,
    const namespacet &ns) const override;

  virtual void output_domain(
    std::ostream &out,
    const namespacet &ns) const override;

  virtual void project_on_vars(
    valuet &value,
    const var_sett &vars,
    exprt &result) override;

  template_kindt &get_template_kind()
  {
    return template_kind;
  }
  domaint *base_domain()
  {
    return base_domain_ptr;
  }

protected:
  domaint *base_domain_ptr;
  template_kindt template_kind;
  disjunctt max;
  templatet templ;
};

#endif // CPROVER_2LS_DOMAINS_DISJUNCTIVE_DOMAIN_H
