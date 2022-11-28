#ifndef _BUILD_H_
#define _BUILD_H_

#include "basis_pms.h"
#include "pms.h"
#include <limits.h>

ISDist::ISDist() {}
/*bool ISDist::parse_parameters1(int argc, char **argv)
{
    int i = 0;
    //cout << "c test1 " << endl;
    int temp_para = 0;

    for (i = 1; i < argc; i++)
    {
        if (0 == strcmp(argv[i], "-seed"))
        {
            i++;
            if (i >= argc)
                return false;
            sscanf(argv[i], "%d", &seed);
        }
        else if (0 == strcmp(argv[i], "-inst"))
        {
            i++;
            if (i >= argc)
                return false;
            file_name = argv[i];
        }
    }
    return true;
}*/

bool ISDist::parse_parameters2(int argc, char **argv)
{
    int i = 0;
    int temp_para = 0;
    // cout << "c test:" << endl;
    for (i = 1; i < argc; i++)
    {
        if (0 == strcmp(argv[i], "-best"))
        {
            i++;
            if (i >= argc)
                return false;
            sscanf(argv[i], "%lld", &best_known);
            cout << "c best_known: " << best_known << endl;
            if (best_known == -1)
            {
                cout << "c no feasible solution" << endl;
                exit(0);
            }
        }
        if (0 == strcmp(argv[i], "-rdprob"))
        {
            i++;
            if (i >= argc)
                return false;
            sscanf(argv[i], "%f", &rdprob);
        }
        else if (0 == strcmp(argv[i], "-bms_num"))
        {
            i++;
            if (i >= argc)
                return false;
            sscanf(argv[i], "%d", &hd_count_threshold);
        }
        else if (0 == strcmp(argv[i], "-rwprob"))
        {
            i++;
            if (i >= argc)
                return false;
            sscanf(argv[i], "%f", &rwprob);
        }
        else if (0 == strcmp(argv[i], "-hard_sp"))
        {
            i++;
            if (i >= argc)
                return false;
            sscanf(argv[i], "%f", &smooth_probability);
        }
        else if (0 == strcmp(argv[i], "-soft_sp"))
        {
            i++;
            if (i >= argc)
                return false;
            sscanf(argv[i], "%f", &soft_smooth_probability);
            cout << "c ssp: " << soft_smooth_probability << endl;
        }
        else if (0 == strcmp(argv[i], "-soft_weight_threshold"))
        {
            i++;
            if (i >= argc)
                return false;
            sscanf(argv[i], "%lf", &softclause_weight_threshold);
            cout << "c soft_weight_threshold: " << softclause_weight_threshold << endl;
        }
        else if (0 == strcmp(argv[i], "-h_inc"))
        {
            i++;
            if (i >= argc)
                return false;
            sscanf(argv[i], "%lf", &h_inc);
        }
        else if (0 == strcmp(argv[i], "-s_inc"))
        {
            i++;
            if (i >= argc)
                return false;
            sscanf(argv[i], "%lf", &s_inc);
        }
        else if (0 == strcmp(argv[i], "-coe"))
        {
            i++;
            if (i >= argc)
                return false;
            sscanf(argv[i], "%d", &coe_soft_clause_weight);
        }
    }
    return true;
}

void ISDist::settings()
{
    best_known = -2;
    local_soln_feasible = 1;
    cutoff_time = 300;

    coe_soft_clause_weight = 3000;
    if (0 == num_hclauses)
    {
        for (int c = 0; c < num_clauses; c++)
        {
            tuned_org_clause_weight[c] = org_clause_weight[c];
        }
    }
    else
    {
        coe_tuned_weight = (double)(coe_soft_clause_weight * num_sclauses) / double(top_clause_weight - 1);
        cout << "c coe_tuned_weight: " << coe_tuned_weight << endl;
        for (int c = 0; c < num_clauses; c++)
        {
            if (org_clause_weight[c] != top_clause_weight)
            {
                tuned_org_clause_weight[c] = (double)org_clause_weight[c] * coe_tuned_weight;
                // cout << tuned_org_clause_weight[c] << " ";
            }
        }
    }
    // cout << endl;

    max_tries = 100000000;
    max_flips = 200000000;
    max_non_improve_flip = 10000000;

    large_clause_count_threshold = 0;
    soft_large_clause_count_threshold = 0;

    // 17
    hd_count_threshold = 25;
    rdprob = 0.036;
    rwprob = 0.48;
    soft_smooth_probability = 9.9E-7;
    smooth_probability = 6.8E-5;
    h_inc = 30;
    s_inc = 10;
    softclause_weight_threshold = 200;

    if (0 == num_hclauses)
    {
        softclause_weight_threshold = 0;
        soft_smooth_probability = 1E-3;
        hd_count_threshold = 22;
        rdprob = 0.036;
        rwprob = 0.48;
        s_inc = 1.0;
    }
}

/*void ISDist::build_neighbor_relation()
{
    int i, j, count;
    int v, c, n;
    int temp_neighbor_count;

    for (v = 1; v <= num_vars; ++v)
    {
        neighbor_flag[v] = 1;
        temp_neighbor_count = 0;

        for (i = 0; i < var_lit_count[v]; ++i)
        {
            c = var_lit[v][i].clause_num;
            for (j = 0; j < clause_lit_count[c]; ++j)
            {
                n = clause_lit[c][j].var_num;
                if (neighbor_flag[n] != 1)
                {
                    neighbor_flag[n] = 1;
                    temp_neighbor[temp_neighbor_count++] = n;
                }
            }
        }

        neighbor_flag[v] = 0;

        var_neighbor[v] = new int[temp_neighbor_count];
        var_neighbor_count[v] = temp_neighbor_count;

        count = 0;
        for (i = 0; i < temp_neighbor_count; i++)
        {
            var_neighbor[v][count++] = temp_neighbor[i];
            neighbor_flag[temp_neighbor[i]] = 0;
        }
    }
}*/

void ISDist::build_instance(char *filename)
{
    total_soft_length = 0;
    total_hard_length = 0;
    // max_soft_weight = 1;
    // min_soft_weight = INT_MAX;
    istringstream iss;
    string line;
    char tempstr1[10];
    char tempstr2[10];

    ifstream infile(filename);
    if (!infile)
    {
        cout << "c the input filename " << filename << " is invalid, please input the correct filename." << endl;
        exit(-1);
    }

    /*** build problem data structures of the instance ***/
    while (getline(infile, line))
    {
        if (line[0] == 'p')
        {
            int read_items;
            num_vars = num_clauses = 0;
            read_items = sscanf(line.c_str(), "%s %s %d %d %lld", tempstr1, tempstr2, &num_vars, &num_clauses, &top_clause_weight);

            if (read_items < 5)
            {
                cout << "read item < 5 " << endl;
                exit(-1);
            }
            break;
        }
    }

    allocate_memory();

    int v, c;
    for (c = 0; c < num_clauses; c++)
    {
        clause_lit_count[c] = 0;
        clause_lit[c] = NULL;
    }
    for (v = 1; v <= num_vars; ++v)
    {
        var_lit_count[v] = 0;
        var_lit[v] = NULL;
        //var_neighbor[v] = NULL;
    }

    int cur_lit;
    c = 0;
    problem_weighted = 0;
    partial = 0;
    num_hclauses = num_sclauses = 0;
    max_clause_length = 0;
    min_clause_length = 100000000;
    unit_clause_count = 0;

    int *redunt_test = new int[num_vars + 1];
    memset(redunt_test, 0, sizeof(int) * num_vars + 1);
    // Now, read the clauses, one at a time.
    while (getline(infile, line))
    {
        if (line[0] == 'c')
            continue;
        else
        {
            iss.clear();
            iss.str(line);
            iss.seekg(0, ios::beg);
        }
        clause_lit_count[c] = 0;

        iss >> org_clause_weight[c];
        if (org_clause_weight[c] != top_clause_weight)
        {
            if (org_clause_weight[c] != 1)
                problem_weighted = 1;
            total_soft_weight += org_clause_weight[c];
            /*if (org_clause_weight[c] > max_soft_weight)
            {
                max_soft_weight = org_clause_weight[c];
            }
            else if (org_clause_weight[c] < min_soft_weight)
            {
                min_soft_weight = org_clause_weight[c];
            }*/
            num_sclauses++;
        }
        else
        {
            num_hclauses++;
            partial = 1;
        }

        iss >> cur_lit;
        int clause_reduent = 0;
        while (cur_lit != 0)
        {
            if (redunt_test[abs(cur_lit)] == 0)
            {
                temp_lit[clause_lit_count[c]] = cur_lit;
                clause_lit_count[c]++;
                redunt_test[abs(cur_lit)] = cur_lit;
            }
            else if (redunt_test[abs(cur_lit)] != cur_lit)
            {
                clause_reduent = 1;
                break;
            }
            iss >> cur_lit;
        }
        if (clause_reduent == 1)
        {
            for (int i = 0; i < clause_lit_count[c]; ++i)
                redunt_test[abs(temp_lit[i])] = 0;

            num_clauses--;
            clause_lit_count[c] = 0;
            continue;
        }

        clause_lit[c] = new clauselit[clause_lit_count[c] + 1];

        int i;
        for (i = 0; i < clause_lit_count[c]; ++i)
        {
            //clause_lit[c][i].clause_num = c;
            clause_lit[c][i].var_num = abs(temp_lit[i]);
            redunt_test[abs(temp_lit[i])] = 0;
            if (temp_lit[i] > 0)
                clause_lit[c][i].sense = 1;
            else
                clause_lit[c][i].sense = 0;

            var_lit_count[clause_lit[c][i].var_num]++;
        }
        clause_lit[c][i].var_num = 0;
        //clause_lit[c][i].clause_num = -1;

        if (clause_lit_count[c] == 1)
        {
            unit_clause[unit_clause_count].clause_num = c;
            unit_clause[unit_clause_count].var_num = clause_lit[c][0].var_num;
            unit_clause[unit_clause_count].sense = clause_lit[c][0].sense;
            unit_clause_count++;
        }
        if (top_clause_weight == org_clause_weight[c])
        {
            total_hard_length += clause_lit_count[c];
        }
        else
        {
            total_soft_length += clause_lit_count[c];
        }
        /*if (clause_lit_count[c] > max_clause_length)
            max_clause_length = clause_lit_count[c];

        if (clause_lit_count[c] < min_clause_length)
            min_clause_length = clause_lit_count[c];
        */
        c++;
    }

    infile.close();

    // creat var literal arrays
    for (v = 1; v <= num_vars; ++v)
    {
        var_lit[v] = new varlit[var_lit_count[v] + 1];
        var_lit_count[v] = 0; // reset to 0, for build up the array
    }
    // scan all clauses to build up var literal arrays
    for (c = 0; c < num_clauses; ++c)
    {
        for (int i = 0; i < clause_lit_count[c]; ++i)
        {
            v = clause_lit[c][i].var_num;
            var_lit[v][var_lit_count[v]].sense = clause_lit[c][i].sense;
            var_lit[v][var_lit_count[v]].clause_num = c;
            ++var_lit_count[v];
        }
    }
    for (v = 1; v <= num_vars; ++v)
        var_lit[v][var_lit_count[v]].clause_num = -1;

    //build_neighbor_relation();

    best_soln_feasible = 0;
}

void ISDist::allocate_memory()
{
    int malloc_var_length = num_vars + 10;
    int malloc_clause_length = num_clauses + 10;

    unit_clause = new lit[malloc_clause_length];

    var_lit = new varlit *[malloc_var_length];
    var_lit_count = new int[malloc_var_length];
    clause_lit = new clauselit *[malloc_clause_length];
    clause_lit_count = new int[malloc_clause_length];

    score = new double[malloc_var_length];
    //var_neighbor = new int *[malloc_var_length];
    //var_neighbor_count = new int[malloc_var_length];
    time_stamp = new long long[malloc_var_length];
    //neighbor_flag = new int[malloc_var_length];
    //temp_neighbor = new int[malloc_var_length];

    org_clause_weight = new long long[malloc_clause_length];
    clause_weight = new double[malloc_clause_length];
    tuned_org_clause_weight = new double[malloc_clause_length];
    sat_count = new int[malloc_clause_length];
    sat_var = new int[malloc_clause_length];
    clause_selected_count = new long long[malloc_clause_length];
    best_soft_clause = new int[malloc_clause_length];

    hardunsat_stack = new int[malloc_clause_length];
    index_in_hardunsat_stack = new int[malloc_clause_length];
    softunsat_stack = new int[malloc_clause_length];
    index_in_softunsat_stack = new int[malloc_clause_length];

    // soft_clause_weight_upper_bound = new long long[malloc_clause_length];

    unsatvar_stack = new int[malloc_var_length];
    index_in_unsatvar_stack = new int[malloc_var_length];
    unsat_app_count = new int[malloc_var_length];

    goodvar_stack = new int[malloc_var_length];
    already_in_goodvar_stack = new int[malloc_var_length];

    cur_soln = new int[malloc_var_length];
    best_soln = new int[malloc_var_length];
    local_opt_soln = new int[malloc_var_length];

    large_weight_clauses = new int[malloc_clause_length];
    soft_large_weight_clauses = new int[malloc_clause_length];
    already_in_soft_large_weight_stack = new int[malloc_clause_length];

    best_array = new int[malloc_var_length];
    temp_lit = new int[malloc_var_length];
}

void ISDist::free_memory()
{
    int i;
    for (i = 0; i < num_clauses; i++)
        delete[] clause_lit[i];

    for (i = 1; i <= num_vars; ++i)
    {
        delete[] var_lit[i];
        //delete[] var_neighbor[i];
    }

    delete[] var_lit;
    delete[] var_lit_count;
    delete[] clause_lit;
    delete[] clause_lit_count;

    delete[] score;
    //delete[] var_neighbor;
    //delete[] var_neighbor_count;
    delete[] time_stamp;
    //delete[] neighbor_flag;
    //delete[] temp_neighbor;

    delete[] org_clause_weight;
    delete[] clause_weight;
    delete[] tuned_org_clause_weight;
    delete[] sat_count;
    delete[] sat_var;
    delete[] clause_selected_count;
    delete[] best_soft_clause;

    delete[] hardunsat_stack;
    delete[] index_in_hardunsat_stack;
    delete[] softunsat_stack;
    delete[] index_in_softunsat_stack;

    delete[] unsatvar_stack;
    delete[] index_in_unsatvar_stack;
    delete[] unsat_app_count;

    delete[] goodvar_stack;
    delete[] already_in_goodvar_stack;

    // delete [] fix;
    delete[] cur_soln;
    delete[] best_soln;
    delete[] local_opt_soln;

    delete[] large_weight_clauses;
    delete[] soft_large_weight_clauses;
    delete[] already_in_soft_large_weight_stack;

    delete[] best_array;
    delete[] temp_lit;

    // delete[] soft_clause_weight_upper_bound;
}

#endif
