/*******************************************************************\

Module: Summarizer

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_H
#define CPROVER_SUMMARIZER_H

#include <util/message.h>
#include <util/options.h>
#include "../ssa/ssa_inliner.h"
#include "../ssa/local_ssa.h"

#include <util/time_stopping.h>

class summarizert : public messaget
{
 public:
 summarizert(const optionst &_options, summary_dbt &_summary_db) : 
    options(_options),
    summary_db(_summary_db),
    solver_instances(0),
    solver_calls(0)
  {}

  typedef summaryt::predicatet preconditiont;
  typedef irep_idt function_namet;
  typedef local_SSAt function_bodyt;
  typedef std::map<function_namet, preconditiont> preconditionst;
  typedef std::map<function_namet, function_bodyt*> functionst;
  typedef functionst::value_type functiont;

  summaryt summarize(functiont &function, const preconditiont &precondition); 
  summaryt summarize(functiont &function);

  void summarize(functionst &functions, const preconditionst &preconditions); 
  void summarize(functionst &functions); 

  void summarize(functionst &functions, const function_namet &entry_function); 

  void inline_summaries(const function_namet &function_name, local_SSAt &SSA, 
                        bool recursive=false, bool always_recompute=false);

  void check_preconditions(const function_namet &function_name, local_SSAt &SSA);

  unsigned get_number_of_solver_instances() { return solver_instances; }
  unsigned get_number_of_solver_calls() { return solver_calls; }

 protected:
  const optionst &options;
  summary_dbt &summary_db;
  functionst functions;
  preconditionst preconditions;

  void run();

  void compute_summary_rec(const function_namet &function_name);

  void join_summaries(const summaryt &existing_summary, summaryt &new_summary);

  void compute_preconditions(const function_namet &function_name, 
			     local_SSAt &SSA);

  unsigned solver_instances;
  unsigned solver_calls;
};


#endif