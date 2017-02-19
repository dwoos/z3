/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

  sine_filter.cpp

Abstract:

  Tactic that performs Sine Qua Non premise selection

Author:

  Doug Woos

Revision History:
--*/

#include "sine_filter.h"
#include "tactical.h"
#include "filter_model_converter.h"
#include "datatype_decl_plugin.h"
#include "rewriter_def.h"
#include "filter_model_converter.h"
#include "extension_model_converter.h"
#include "var_subst.h"
#include "ast_util.h"
#include "obj_pair_hashtable.h"
#include "ast_pp.h"
#include "timeit.h"

class sine_tactic : public tactic {

    ast_manager&  m;
    params_ref    m_params;

public:

    sine_tactic(ast_manager& m, params_ref const& p): 
        m(m), m_params(p) {}
    
    virtual tactic * translate(ast_manager & m) {
        return alloc(sine_tactic, m, m_params);
    }

    virtual void updt_params(params_ref const & p) {
    }

    virtual void collect_param_descrs(param_descrs & r) {
    }

    virtual void operator()(goal_ref const & g,
                            goal_ref_buffer & result,
                            model_converter_ref & mc,
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        
        mc = 0; pc = 0; core = 0;

        TRACE("sine", tout << "goal size before: " << g->size(););
        ptr_vector<expr> new_forms;

        
        filter_expressions(g, new_forms);
        TRACE("sine", tout << "goal size after: " << new_forms.size(););
        g->reset();
        for (unsigned i = 0; i < new_forms.size(); i++) {
            g->assert_expr(new_forms.get(i), 0, 0);
        }
        g->inc_depth();
        g->updt_prec(goal::OVER);
        result.push_back(g.get());
        SASSERT(g->is_well_sorted());
        filter_model_converter * fmc = alloc(filter_model_converter, m);
        mc = fmc;
    }
    
    virtual void cleanup() {
    }

private:

    typedef std::pair<expr*,expr*> t_work_item;

    t_work_item work_item(expr *e, expr *root) {
        return std::pair<expr*, expr*>(e, root);
    }

    bool quantifier_matches(quantifier *q,
                            obj_hashtable<func_decl> const & consts,
                            ptr_vector<func_decl> & next_consts) {
        TRACE("sine_detail", tout << "size of consts is "; tout << consts.size(); tout << "\n";);
        for (obj_hashtable<func_decl>::iterator constit = consts.begin(), constend = consts.end(); constit != constend; constit++) {
            TRACE("sine_detail", tout << *constit; tout << "\n";);
        }
        bool matched = false;
        for (unsigned i = 0; i < q->get_num_patterns(); i++) {
            bool p_matched = true;
            ptr_vector<expr> stack;
            expr *curr;
            // patterns are wrapped with "pattern"
            if (!m.is_pattern(q->get_pattern(i), stack)) {
                continue;
            }
            while (!stack.empty()) {
                curr = stack.back();
                stack.pop_back();
                if (is_app(curr)) {
                    app *a = to_app(curr);
                    func_decl *f = a->get_decl();
                    if (!consts.contains(f)) {
                        TRACE("sine_detail", tout << mk_pp(f, m) << "\n";);
                        p_matched = false;
                        next_consts.push_back(f);
                        break;
                    }
                    for (unsigned j = 0; j < a->get_num_args(); j++) {
                        stack.push_back(a->get_arg(j));
                    }
                }
            }
            if (p_matched) {
                matched = true;
                break;
            }
        }
        return matched;
    }
  
    void filter_expressions(goal_ref const & g, ptr_vector<expr> & new_exprs) {
        //timeit tt(true, "sine_filter.filter_expressions");
        obj_map<func_decl, obj_hashtable<expr> > const2exp;
        obj_map<expr, obj_hashtable<func_decl> > exp2const;
        obj_map<func_decl, obj_pair_hashtable<expr, expr> > const2quantifier;
        obj_hashtable<func_decl> consts;
        vector<t_work_item> stack;
        for (unsigned i = 0; i < g->size(); i++) {
            stack.push_back(work_item(g->form(i), g->form(i)));
        }
        t_work_item curr;
        while (!stack.empty()) {
            curr = stack.back();
            stack.pop_back();
            if (!exp2const.contains(curr.second)) {
              exp2const.insert(curr.second, obj_hashtable<func_decl>());
            }
            if (is_app(curr.first)) {
                app *a = to_app(curr.first);
                if (is_uninterp(a)) {
                    func_decl *f = a->get_decl();
                    if (!consts.contains(f)) {
                        consts.insert(f);
                        if (const2quantifier.contains(f)) {
                            for (obj_pair_hashtable<expr, expr>::iterator it = const2quantifier[f].begin(), end = const2quantifier[f].end(); it != end; it++) {
                                stack.push_back(*it);
                            }
                            const2quantifier.remove(f);
                        }
                    }
                    if (!const2exp.contains(f)) {
                        const2exp.insert(f, obj_hashtable<expr>());
                    }
                    if (!const2exp[f].contains(curr.second)) {
                        const2exp[f].insert(curr.second);
                    }
                    if (!exp2const[curr.second].contains(f)) {
                        exp2const[curr.second].insert(f);
                    }
                }
                for (unsigned i = 0; i < a->get_num_args(); i++) {
                    stack.push_back(work_item(a->get_arg(i), curr.second));
                }
            }
            else if (is_quantifier(curr.first)) {
                quantifier *q = to_quantifier(curr.first);
                if (q->is_forall()) {
                    if (q->has_patterns()) {
                        ptr_vector<func_decl> next_consts;
                        if (quantifier_matches(q, consts, next_consts)) {
                            stack.push_back(work_item(q->get_expr(), curr.second));
                        }
                        else {
                            for (unsigned i = 0; i < next_consts.size(); i++) {
                                func_decl *c = next_consts.get(i);
                                if (!const2quantifier.contains(c)) {
                                    const2quantifier.insert(c, obj_pair_hashtable<expr, expr>());
                                }
                                if (!const2quantifier[c].contains(curr)) {
                                    const2quantifier[c].insert(curr);
                                }
                            }
                        }
                    }
                    else {
                        stack.push_back(work_item(q->get_expr(), curr.second));
                    }
                }
                else if (q->is_exists()) {
                    stack.push_back(work_item(q->get_expr(), curr.second));
                }
            }
        }
        // ok, now we just need to find the connected component of the last term
    
        obj_hashtable<expr> visited;
        ptr_vector<expr> to_visit;
        to_visit.push_back(g->form(g->size() - 1));
        visited.insert(g->form(g->size() - 1));
        expr *visiting;
        while (!to_visit.empty()) {
            visiting = to_visit.back();
            to_visit.pop_back();
            for (obj_hashtable<func_decl>::iterator constit = exp2const[visiting].begin(), constend = exp2const[visiting].end(); constit != constend; constit++) {
                for (obj_hashtable<expr>::iterator exprit = const2exp[*constit].begin(), exprend = const2exp[*constit].end(); exprit != exprend; exprit++) {
                    if (!visited.contains(*exprit)) {
                        to_visit.push_back(*exprit);
                        visited.insert(*exprit);
                    }
                }
            }
        }
        for (unsigned i = 0; i < g->size(); i++) {
            if (visited.contains(g->form(i))) {
                new_exprs.push_back(g->form(i));
            }
        }
    }
};

tactic * mk_sine_tactic(ast_manager & m, params_ref const & p) {
    return alloc(sine_tactic, m, p);
}
