#ifndef _HEURISTIC_H_
#define _HEURISTIC_H_

#include "basis_pms.h"
#include "deci.h"
#include "propagate.h"
#include <map>

void ISDist::local_search_with_decimation(char *inputfile)
{
    param_settings();
    Decimation deci(var_lit, var_lit_count, clause_lit, org_clause_weight, top_clause_weight);
    deci.make_space(num_clauses, num_vars);
    opt_unsat_weight = __LONG_LONG_MAX__;
    for (tries = 1; tries < max_tries; ++tries) {
        deci.init(local_opt_soln, best_soln, unit_clause, unit_clause_count, clause_lit_count);
        deci.unit_prosess();
        init(deci.fix);

        local_opt = __LONG_LONG_MAX__;
        max_flips = max_non_improve_flip;
        for (step = 1; step < max_flips; ++step) {
            if (hard_unsat_nb == 0) {
                update_best_soln();
                print_best_solution();

            }
            int flipvar = pick_var();
            if (flipvar == 0) { continue; }
            flip(flipvar);
            time_stamp[flipvar] = step;
            total_step++;

            // if about to quit, make a final attempt

            if (use_final_attempt && step + 1 >= max_flips && final_attempt_state < final_attempt_looptime && best_soln_feasible) {
                final_attempt_state++;
                final_attempt_attempt++;
                max_flips += final_attempt_step;
                for (int v = 1; v <= num_vars; ++v) {
                    if (cur_soln[v] != best_soln[v]) {
                        flip(v);
                        time_stamp[v] = step;
                    }
                }
                systematic_search();
            }
        }
        print_best_solution();
    }
}

void ISDist::param_settings() {
    if (1 == problem_weighted)
    {
        if (total_soft_length / num_sclauses > 100)
        {
            //cout << "c avg_soft_length: " << total_soft_length / num_sclauses << endl;
            h_inc = 300;
            s_inc = 100;
        }
        if (0 != num_hclauses)
        {
            coe_tuned_weight = (double)(coe_soft_clause_weight * num_sclauses) / double(top_clause_weight - 1);
            for (int c = 0; c < num_clauses; c++)
            {
                if (org_clause_weight[c] != top_clause_weight)
                {
                    tuned_org_clause_weight[c] = (double)org_clause_weight[c] * coe_tuned_weight;
                }
            }
        }
        else
        {
            softclause_weight_threshold = 0;
            soft_smooth_probability = 1E-3;
            hd_count_threshold = 22;
            rdprob = 0.036;
            rwprob = 0.48;
            s_inc = 1.0;
            for (int c = 0; c < num_clauses; c++)
            {
                tuned_org_clause_weight[c] = org_clause_weight[c];
            }
        }
    }
    else
    {
        if (0 == num_hclauses)
        {
            hd_count_threshold = 94;
            coe_soft_clause_weight = 397;
            rdprob = 0.007;
            rwprob = 0.047;
            soft_smooth_probability = 0.002;
            softclause_weight_threshold = 550;
        }
    }
}

void ISDist::init(vector<int> &init_solution)
{
    local_optima_thres = init_local_optima_thres;
    local_optima_count = 0;
    soft_large_weight_clauses_count = 0;
    if (1 == problem_weighted) // weighted partial MaxSAT
    {
        if (0 != num_hclauses)
        {
            if ((0 == local_soln_feasible || 0 == best_soln_feasible))
            {
                for (int c = 0; c < num_clauses; c++)
                {
                    already_in_soft_large_weight_stack[c] = 0;
                    clause_selected_count[c] = 0;
                    clause_weight[c] = 1;
                }
            }
            else
            {
                for (int c = 0; c < num_clauses; c++)
                {
                    already_in_soft_large_weight_stack[c] = 0;
                    clause_selected_count[c] = 0;

                    if (org_clause_weight[c] == top_clause_weight)
                        clause_weight[c] = 1;
                    else
                    {
                        clause_weight[c] = tuned_org_clause_weight[c];
                        if (clause_weight[c] > s_inc && already_in_soft_large_weight_stack[c] == 0)
                        {
                            already_in_soft_large_weight_stack[c] = 1;
                            soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
                        }
                    }
                }
            }
        }
        else
        {
            for (int c = 0; c < num_clauses; c++)
            {
                already_in_soft_large_weight_stack[c] = 0;
                clause_selected_count[c] = 0;
                clause_weight[c] = tuned_org_clause_weight[c];
                if (clause_weight[c] > s_inc && already_in_soft_large_weight_stack[c] == 0)
                {
                    already_in_soft_large_weight_stack[c] = 1;
                    soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
                }
            }
        }
    }
    else // unweighted partial MaxSAT
    {
        for (int c = 0; c < num_clauses; c++)
        {
            already_in_soft_large_weight_stack[c] = 0;
            clause_selected_count[c] = 0;

            if (org_clause_weight[c] == top_clause_weight)
                clause_weight[c] = 1;
            else
            {
                if ((0 == local_soln_feasible || 0 == best_soln_feasible) && num_hclauses > 0)
                {
                    clause_weight[c] = 1;
                }
                else
                {
                    clause_weight[c] = coe_soft_clause_weight;
                    if (clause_weight[c] > 1 && already_in_soft_large_weight_stack[c] == 0)
                    {
                        already_in_soft_large_weight_stack[c] = 1;
                        soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
                    }
                }
            }
        }
    }

    if (init_solution.size() == 0)
    {
        for (int v = 1; v <= num_vars; v++)
        {
            cur_soln[v] = rand() % 2;
            time_stamp[v] = 0;
            unsat_app_count[v] = 0;
        }
    }
    else
    {
        for (int v = 1; v <= num_vars; v++)
        {
            cur_soln[v] = init_solution[v];
            if (cur_soln[v] != 0 && cur_soln[v] != 1)
                cur_soln[v] = rand() % 2;
            time_stamp[v] = 0;
            unsat_app_count[v] = 0;
        }
    }
    local_soln_feasible = 0;
    // init stacks
    hard_unsat_nb = 0;
    soft_unsat_weight = 0;
    hardunsat_stack_fill_pointer = 0;
    softunsat_stack_fill_pointer = 0;
    unsatvar_stack_fill_pointer = 0;
    large_weight_clauses_count = 0;

    /* figure out sat_count, sat_var and init unsat_stack */
    for (int c = 0; c < num_clauses; ++c)
    {
        sat_count[c] = 0;
        for (int j = 0; j < clause_lit_count[c]; ++j)
        {
            if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
            {
                sat_count[c]++;
                sat_var[c] = clause_lit[c][j].var_num;
            }
        }
        if (sat_count[c] == 0)
        {
            unsat(c);
        }
    }

    /*figure out score*/
    for (int v = 1; v <= num_vars; v++)
    {
        score[v] = 0.0;
        for (int i = 0; i < var_lit_count[v]; ++i)
        {
            int c = var_lit[v][i].clause_num;
            if (sat_count[c] == 0)
                score[v] += clause_weight[c];
            else if (sat_count[c] == 1 && var_lit[v][i].sense == cur_soln[v])
                score[v] -= clause_weight[c];
        }
    }

    // init goodvars stack
    goodvar_stack_fill_pointer = 0;
    for (int v = 1; v <= num_vars; v++)
    {
        if (score[v] > 0)
        {
            already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
            mypush(v, goodvar_stack);
        }
        else
            already_in_goodvar_stack[v] = -1;
    }
    propagate_record.clear();
    final_attempt_state = 0;
}

double ISDist::get_curr_punish() {
    double curr_punish = 0;
    for (int i = 0; i < hardunsat_stack_fill_pointer; ++i) {
        int c = hardunsat_stack[i];
        curr_punish += clause_weight[c];
    }
    for (int i = 0; i < softunsat_stack_fill_pointer; ++i) {
        int c = softunsat_stack[i];
        curr_punish += clause_weight[c];
    }
    return curr_punish;
}

int ISDist::systematic_search()
{
    auto scores = CandFilter<int, double, long long>(num_cand_in_propagate);
    bool current_feasible = (hardunsat_stack_fill_pointer == 0);
    int num_visited = 0;
    double curr_punish = get_curr_punish();

    if (current_feasible) {
        int rand_start_index = rand() % softunsat_stack_fill_pointer;
        int rand_end_index = rand_start_index + softunsat_stack_fill_pointer;
        for (int t = rand_start_index; t < rand_end_index && num_visited < hd_count_threshold; ++t) {
            int c = softunsat_stack[t % softunsat_stack_fill_pointer];
            for (int i = 0; i < clause_lit_count[c]; ++i) {
                auto v = clause_lit[c][i].var_num;
                scores.Insert(v, score[v], time_stamp[v]);
                num_visited++;
            }
        }
    } else {
        int rand_start_index = rand() % hardunsat_stack_fill_pointer;
        int rand_end_index = rand_start_index + hardunsat_stack_fill_pointer;
        for (int t = rand_start_index; t < rand_end_index && num_visited < hd_count_threshold; ++t) {
            int c = hardunsat_stack[t % hardunsat_stack_fill_pointer];
            for (int i = 0; i < clause_lit_count[c]; ++i) {
                // all lits are falsified because this is MaxSAT instance
                auto v = clause_lit[c][i].var_num;
                scores.Insert(v, score[v], time_stamp[v]);
                num_visited++;
            }
        }
    }
    if (scores.IsEmpty()) { return 0; }
    double res = 0;
    double best_res = 1e300;
    int best_res_v = 0;
    for (int v : scores.itemVec) {
        res = backtrack_impl(v, curr_punish);
        if (res <= 0) { break; }
        if (res < best_res) {
            best_res = res;
            best_res_v = v;
        }
    }
    if (best_res <= 0) {
        local_optima_thres = init_local_optima_thres;
        return 1;
    } else {
        if (local_optima_thres < init_local_optima_thres * local_optima_thres_multiplier)
            local_optima_thres *= 2;
    }
    return 0;
}

void ISDist::flip_up(int v) {
    auto& UP = get_table(v, 1-cur_soln[v]);
    time_stamp[v] = step;
    flip(v);
    for (auto& vws : UP) {
        int v2 = vws.id;
        if (cur_soln[v2] != vws.sense) {
            time_stamp[v2] = step;
            flip(v2);
        }
    }
}

void ISDist::flip_up(int v, map<int, long long>& former_time_stamp, FlipRecord& record) {
    auto& UP = get_table(v, 1-cur_soln[v]);
    former_time_stamp[v] = time_stamp[v];
    time_stamp[v] = step;
    flip(v);
    record.push(v);
    for (auto& vws : UP) {
        int v2 = vws.id;
        if (cur_soln[v2] != vws.sense) {
            former_time_stamp[v2] = time_stamp[v2];
            time_stamp[v2] = step; // avoid being flipped back
            flip(v2);
            record.push(v2);
            if (use_propagate_size_limit && record.size > propagate_size_limit)
            { break; }
        }
    }
}

double ISDist::backtrack_impl(int best_var, double last_punish) {
    if (final_attempt_state == 0) {
        num_local_optima++;
    }
    map<int, long long> former_time_stamp;
    propagate_record.clear();
    flip_up(best_var, former_time_stamp, propagate_record);

    while (goodvar_stack_fill_pointer > 0) {
        int v = pick_var();
        propagate_record.push(v);
        former_time_stamp[v] = time_stamp[best_var];
        time_stamp[v] = step; // avoid being flipped back
        flip(v);
        if (hardunsat_stack_fill_pointer == 0 && soft_unsat_weight < opt_unsat_weight) { break; }
    }

    if (propagate_record.size == 0) {
        for (auto& pair: former_time_stamp) {
            auto v = pair.first;
            time_stamp[v] = pair.second;
        }
        if (final_attempt_state == 0) {
            num_backtrack++;
        }
        while (goodvar_stack_fill_pointer > 0) {
            goodvar_stack_fill_pointer--;
            already_in_goodvar_stack[goodvar_stack_fill_pointer] = -1;
        }
        return 1e300;
    }

    double punish = get_curr_punish();

    if (punish + double_tol < last_punish || (punish - double_tol < last_punish && propagate_record.size > 1)) {
        // success
        if (final_attempt_state == 0) {
            propagate_succ_len += propagate_record.size;
        }
        total_step += propagate_record.size;
        for (auto& pair: former_time_stamp) {
            auto v = pair.first;
            if (score[v] > 0 && already_in_goodvar_stack[v] == -1) {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v, goodvar_stack);
            }
        }
        propagate_record.clear();
        // ss_succ_count[period]++;
    } else {  // failure
        if (final_attempt_state == 0) {
            propagate_fail_len += propagate_record.size;
        }
        while (propagate_record.size > 0) {
            int v = propagate_record.tail();
            propagate_record.remove_tail();
            flip(v);
        }
        reset_time_stamp(former_time_stamp);
       if (final_attempt_state == 0){
           num_backtrack++;
       }
       while (goodvar_stack_fill_pointer > 0) {
           goodvar_stack_fill_pointer--;
           already_in_goodvar_stack[goodvar_stack_fill_pointer] = -1;
       }
    }
    return punish - last_punish;
}

void ISDist::reset_time_stamp(map<int, long long>& former_time_stamp) {
    for (auto& pair: former_time_stamp) {
        auto v = pair.first;
        time_stamp[v] = pair.second;
    }
}

int ISDist::pick_var()
{
    int i, v;
    int best_var;
    int sel_c;
    lit *p;

    if (goodvar_stack_fill_pointer > 0)
    {
        if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rdprob)
            return goodvar_stack[rand() % goodvar_stack_fill_pointer];

        if (goodvar_stack_fill_pointer < hd_count_threshold)
        {
            best_var = goodvar_stack[0];

            for (i = 1; i < goodvar_stack_fill_pointer; ++i)
            {
                v = goodvar_stack[i];
                if (score[v] > score[best_var])
                {
                    best_var = v;
                }
                else if (score[v] == score[best_var])
                {
                    if (time_stamp[v] < time_stamp[best_var])
                    {
                        best_var = v;
                    }
                }
            }
            return best_var; // best_array[rand() % best_array_count];
        }
        else
        {
            best_var = goodvar_stack[rand() % goodvar_stack_fill_pointer];

            for (i = 1; i < hd_count_threshold; ++i)
            {
                v = goodvar_stack[rand() % goodvar_stack_fill_pointer];
                if (score[v] > score[best_var])
                {
                    best_var = v;
                }
                else if (score[v] == score[best_var])
                {
                    if (time_stamp[v] < time_stamp[best_var])
                    {
                        best_var = v;
                    }
                }
            }
            return best_var; // best_array[rand() % best_array_count];
        }
    }

    if (use_runtime_unit_propagate && local_optima_count > local_optima_thres && final_attempt_state == 0) {
        local_optima_count = 0;
        systematic_search();
        return 0;
    }

    update_clause_weights();
    local_optima_count++;
    if (hardunsat_stack_fill_pointer > 0)
    {
        sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
    }
    else
    {
        sel_c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
    }
    if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
        return clause_lit[sel_c][rand() % clause_lit_count[sel_c]].var_num;

    best_var = clause_lit[sel_c][0].var_num;
    p = clause_lit[sel_c];
    for (p++; (v = p->var_num) != 0; p++)
    {
        if (score[v] > score[best_var])
            best_var = v;
        else if (score[v] == score[best_var])
        {
            if (time_stamp[v] < time_stamp[best_var])
                best_var = v;
        }
    }

    return best_var;
}

void ISDist::update_best_soln() {
    local_soln_feasible = 1;
    if (local_opt > soft_unsat_weight)
    {
        local_opt = soft_unsat_weight;
        max_flips = step + max_non_improve_flip;
        for (int v = 1; v <= num_vars; ++v)
            local_opt_soln[v] = cur_soln[v];
    }
    if (soft_unsat_weight < opt_unsat_weight)
    {
        opt_time = get_runtime();
        cout << "o " << soft_unsat_weight << " " << total_step << " " << tries << " " << opt_time << endl;
        opt_unsat_weight = soft_unsat_weight;

        for (int v = 1; v <= num_vars; ++v)
            best_soln[v] = cur_soln[v];
        if (opt_unsat_weight <= best_known)
        {
            cout << "c best solution found." << endl;
            if (opt_unsat_weight < best_known)
            {
                cout << "c a better solution " << opt_unsat_weight << endl;
            }
            return;
        }
        if (final_attempt_state > 0) {
            // which means the better soln is found in final attempt steps
            final_attempt_success++;
            final_attempt_state = 0;
        }
        opt_soln_update_history.push_back(opt_unsat_weight);
        opt_soln_update_time.push_back(opt_time);
    }
    best_soln_feasible = 1;
}

void ISDist::hard_increase_weights()
{
    int i, c, v;
    for (i = 0; i < hardunsat_stack_fill_pointer; ++i)
    {
        c = hardunsat_stack[i];
        clause_weight[c] += h_inc;

        if (clause_weight[c] == (h_inc + 1))
            large_weight_clauses[large_weight_clauses_count++] = c;

        for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
        {
            score[v] += h_inc;
            if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
            {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v, goodvar_stack);
            }
        }
    }
    return;
}

void ISDist::soft_increase_weights()
{
    int i, c, v;

    if (1 == problem_weighted)
    {
        for (i = 0; i < softunsat_stack_fill_pointer; ++i)
        {
            c = softunsat_stack[i];
            if (clause_weight[c] >= tuned_org_clause_weight[c] + softclause_weight_threshold)
                continue;
            else
                clause_weight[c] += s_inc;

            if (clause_weight[c] > s_inc && already_in_soft_large_weight_stack[c] == 0)
            {
                already_in_soft_large_weight_stack[c] = 1;
                soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
            }
            for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
            {
                score[v] += s_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    else
    {
        for (i = 0; i < softunsat_stack_fill_pointer; ++i)
        {
            c = softunsat_stack[i];
            if (clause_weight[c] >= coe_soft_clause_weight + softclause_weight_threshold)
                continue;
            else
                clause_weight[c] += s_inc;

            if (clause_weight[c] > s_inc && already_in_soft_large_weight_stack[c] == 0)
            {
                already_in_soft_large_weight_stack[c] = 1;
                soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
            }
            for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
            {
                score[v] += s_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    return;
}

void ISDist::hard_smooth_weights()
{
    int i, clause, v;
    for (i = 0; i < large_weight_clauses_count; i++)
    {
        clause = large_weight_clauses[i];
        if (sat_count[clause] > 0)
        {
            clause_weight[clause] -= h_inc;

            if (clause_weight[clause] == 1)
            {
                large_weight_clauses[i] = large_weight_clauses[--large_weight_clauses_count];
                i--;
            }
            if (sat_count[clause] == 1)
            {
                v = sat_var[clause];
                score[v] += h_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    return;
}

void ISDist::soft_smooth_weights()
{
    int i, clause, v;

    for (i = 0; i < soft_large_weight_clauses_count; i++)
    {
        clause = soft_large_weight_clauses[i];
        if (sat_count[clause] > 0)
        {
            clause_weight[clause] -= s_inc;
            if (clause_weight[clause] <= s_inc && already_in_soft_large_weight_stack[clause] == 1)
            {
                already_in_soft_large_weight_stack[clause] = 0;
                soft_large_weight_clauses[i] = soft_large_weight_clauses[--soft_large_weight_clauses_count];
                i--;
            }
            if (sat_count[clause] == 1)
            {
                v = sat_var[clause];
                score[v] += s_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    return;
}

void ISDist::update_clause_weights()
{
    if (num_hclauses > 0)
    {
        // update hard clause weight
        if (1 == local_soln_feasible && ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < smooth_probability && large_weight_clauses_count > large_clause_count_threshold)
        {
            hard_smooth_weights();
        }
        else
        {
            hard_increase_weights();
        }

        // update soft clause weight
        // if (1 == local_soln_feasible && ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < soft_smooth_probability && soft_large_weight_clauses_count > soft_large_clause_count_threshold)
        if (soft_unsat_weight >= opt_unsat_weight)
        {
            if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < soft_smooth_probability && soft_large_weight_clauses_count > soft_large_clause_count_threshold)
            {
                soft_smooth_weights();
            }
            else if (0 == hard_unsat_nb)
            {
                soft_increase_weights();
            }
        }
    }
    else
    {
        if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < soft_smooth_probability && soft_large_weight_clauses_count > soft_large_clause_count_threshold)
        {
            soft_smooth_weights();
        }
        else
        {
            soft_increase_weights();
        }
    }
}

#endif
