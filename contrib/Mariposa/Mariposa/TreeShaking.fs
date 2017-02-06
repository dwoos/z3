module TreeShaking
open SMTLib
open System
open System.Collections.Generic
open Util

let canon (i : ident) = fst i

let get_env (bindings : (ident * expr) list) : string list =
    List.map canon (List.map fst bindings)

type state = {
    work_list : Queue<(expr * string list * int)>;
    stmts : Dictionary<stmt, int>;
    stmts_rev : Dictionary<int, stmt>
    ambient_constants : HashSet<string>;
    stmt_constants : Dictionary<int, HashSet<string>>;
    constant_stmts : Dictionary<string, HashSet<int>>;
    quantifiers : Dictionary<string, List<(expr * string list * int)>>
    }

let make_state () =
    { work_list = new Queue<(expr * string list * int)>();
      stmts = new Dictionary<stmt, int>();
      stmts_rev = new Dictionary<int, stmt>();
      ambient_constants = new HashSet<string>();
      stmt_constants = new Dictionary<int, HashSet<string>>();
      constant_stmts = new Dictionary<string, HashSet<int>>();
      quantifiers = new Dictionary<string, List<(expr * string list * int)>>()
    }

type pattern_match =
    | Match
    | NoMatch of string list

let patterns_match (st : state) (pats : string list list) =
    let rec patterns_match' firsts pats =
        match pats with
        | [] -> NoMatch firsts
        | [] :: _ ->
            Match
        | (c :: pat) :: pats' ->
            if st.ambient_constants.Contains(c) then
                patterns_match' firsts (pat :: pats')
            else
                patterns_match' (c :: firsts) pats'
    patterns_match' [] pats

let add_kv (d : Dictionary<'K, List<'V>>) k v =
    if d.ContainsKey k then
        d.[k].Add(v)
    else
        d.Add(k, new List<'V>())
        d.[k].Add(v)

let add_kv_s (d : Dictionary<'K, HashSet<'V>>) k v =
    if d.ContainsKey k then
        d.[k].Add(v) |> ignore
    else
        d.Add(k, new HashSet<'V>())
        d.[k].Add(v) |> ignore



// Adds c to ambient constants and, if necessary, to the work list
let add_constant st c id =
    st.ambient_constants.Add(c) |> ignore
    add_kv_s st.stmt_constants id c
    add_kv_s st.constant_stmts c id
    if st.quantifiers.ContainsKey(c) then
        for q in st.quantifiers.[c] do
            st.work_list.Enqueue q
        st.quantifiers.Remove(c) |> ignore

// c is the first non-matching constant.
// c should never be in ambient_constants.
let add_quantifier st e env cs id =
    cs |> List.iter (fun c -> add_kv st.quantifiers c (e, env, id))

let rec get_patterns (annots : expr annotation list) =
    match annots with
    | Pattern es :: annots' -> es :: get_patterns annots'
    | _ :: annots' -> get_patterns annots'
    | [] -> []

let (|WithPatterns|_|) (e : expr) =
    match e with
    | Annot(annots, body) ->
        let pats = get_patterns annots
        if List.isEmpty pats then
            None
        else
            Some(body, pats)
    | _ -> None

// Only need to look at terms that show up in patterns
let rec get_pattern_constants env e =
    match e with
    | Id(i) when not (List.contains (canon i) env) ->
        [canon i]
    | Lst(l) ->
        List.collect (get_pattern_constants env) l
    | _ -> []


let rec process_expr (st : state) (id : int) (env : string list) (e : expr) =
    match e with
    | Id(i) when not (List.contains (canon i) env) ->
        add_constant st (canon i) id
    | Lst(l) ->
        List.iter (process_expr st id env) l
    | Annot(annots, e) ->
        process_expr st id env e
    | Not(e) ->
        process_expr st id env e
    | And(l) ->
        List.iter (process_expr st id env) l
    | Or(l) ->
        List.iter (process_expr st id env) l
    | Implies(e1, e2) ->
        process_expr st id env e1
        process_expr st id env e2
    | Eq(e1, e2) ->
        process_expr st id env e1
        process_expr st id env e2
    | Let(bindings, body) | Exists (bindings, body) ->
        bindings |> List.map snd |> List.iter (process_expr st id env)
        process_expr st id (env @ get_env bindings) body
    | Forall(bindings, body) ->
        let env' = env @ get_env bindings
        match body with
        | WithPatterns(inner, patterns) ->
            let pats = patterns |> List.map Lst |>
                       List.map (get_pattern_constants env')
            match patterns_match st pats with
            | Match ->
                process_expr st id env' inner
            | NoMatch cs ->
                add_quantifier st e env cs id
        | _ ->
            process_expr st id env' body
    | Val(_) -> ()
    | Id(_) -> ()

let rec process_exprs st =
    while st.work_list.Count <> 0 do
        let (e, env, id) = st.work_list.Dequeue()
        process_expr st id env e

let isAssert s =
    match s with
    | Assert(e) -> true
    | _ -> false

let is_filterable_stmt s =
    match s with
    | Assert _ -> true
    | DefineFun _ -> true
    //| DeclareFun _ -> true
    | _ -> false

let add_stmt st id s =
    if not (st.stmts.ContainsKey(s)) then
        st.stmts.Add(s, id)
        st.stmts_rev.Add(id, s)
        match s with
        | Assert e ->
            st.work_list.Enqueue(e, [], id)
        // don't filter declare-fun for now, since we might need it even if not in closure (because of binders :( ).
        (*| DeclareFun(name, _, _) ->
            // we *don't* want to add this to ambient_constants.
            add_kv_s st.stmt_constants id (canon name)
            add_kv_s st.constant_stmts (canon name) id*)
        | DefineFun(name, bindings, body, ret) ->
            add_kv_s st.stmt_constants id (canon name)
            add_kv_s st.constant_stmts (canon name) id
            st.work_list.Enqueue(body, get_env bindings, id)
        | _ -> ()

let dict_hashset_to_dict_set (d : Dictionary<'K, HashSet<'V>>) =
    let d' = new Dictionary<'K, Set<'V>>()
    for k_v in d do
        d'.Add(k_v.Key, set k_v.Value)
    d'

let connected_component_old (v_e : Dictionary<'V, Set<'E>>) (e_v : Dictionary<'E, Set<'V>>) v =
    let rec connected_component' visited tovisit =
        match tovisit with
        | [] -> visited
        | v :: vs ->
            let edges = v_e.[v]
            let neighbors = edges |> Seq.map (fun e -> e_v.[e]) |> Set.unionMany
            let unvisited = neighbors |> Set.filter (fun v -> not (Set.contains v visited))
            connected_component' (Set.add v visited) (vs @ Set.toList unvisited)
    connected_component' Set.empty [v]

let connected_component (v_e : Dictionary<'V, HashSet<'E>>) (e_v : Dictionary<'E, HashSet<'V>>) prohibited_edges vs =
    let visited = new HashSet<'V>()
    let tovisit = new Queue<'V>()
    for v in vs do
        tovisit.Enqueue(v)
        visited.Add(v) |> ignore
    while tovisit.Count <> 0 do
        let v = tovisit.Dequeue()
        let edges = v_e.[v]
        for e in edges do
            let neighbors = e_v.[e]
            for neighbor in neighbors do
                if not (visited.Contains(neighbor)) then
                    visited.Add(neighbor) |> ignore
                    if not (Set.contains e prohibited_edges) then
                        tovisit.Enqueue(neighbor)
    visited


let find_constants ss =
    let id = ref 0
    let st = make_state()
    ss |> List.iter (fun s -> if is_filterable_stmt s then
                                  add_stmt st !id s
                                  id := !id + 1)
    process_exprs st
    st

let query_closure prohibited st queries =
    connected_component st.stmt_constants
                        st.constant_stmts
                        prohibited
                        queries |> set

let should_keep st closure s =
    (not (is_filterable_stmt s)) || (Set.contains (st.stmts.[s]) closure)

let process_stmts prohibited ss =
    let groups = split is_reset ss
    let sts = groups |> List.map find_constants
    let closures = sts |> List.map (fun st -> query_closure prohibited st [st.stmts.Count - 1])
    let filtered_groups = List.map3 (fun group st closure -> List.filter (should_keep st closure) group)
                                    groups sts closures
    join Reset filtered_groups

let find_fstar_queries ss =
    List.filter (fun s ->
                 match s with
                 | Assert (Annot (annots, e)) ->
                   List.exists (fun ann ->
                                match ann with
                                | Named (name, _) ->
                                  if name.StartsWith "@query_" then
                                      true
                                  else false
                                | _ -> false) annots
                 | _ -> false) ss

let process_stmts_fstar prohibited ss =
    let st = find_constants ss
    let queries = ss |> find_fstar_queries |> List.map (fun c -> st.stmts.[c])
    let closure = query_closure prohibited st queries
    List.filter (should_keep st closure) ss
    
