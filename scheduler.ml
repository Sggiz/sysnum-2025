open Netlist_ast
open Graph

exception Combinational_cycle

let read_exp ((_, exp): equation) = 
  let read_arg arg =
    match arg with
    |Avar(i) -> [i]
    |Aconst(_) -> []
  in

  let read_union =
    List.fold_left (fun l a -> read_arg a @ l) []
  in
  
  match exp with
  |Earg(arg) -> read_arg arg
  |Ereg(_) -> []
  |Enot(arg) -> read_arg arg
  |Ebinop(_,a1,a2) -> read_arg a1 @ read_arg a2
  |Emux(a1,a2,a3) -> read_arg a1 @ read_arg a2 @ read_arg a3
  |Erom(_,_,arg) -> read_arg arg
  |Eram(_,_,arg,_,_,_) -> read_arg arg
  |Econcat(a1, a2) -> read_union [a1;a2]
  |Eslice(_,_,arg) -> read_arg arg
  |Eselect(_,arg) -> read_arg arg


let programm_to_graph p =
  let g = mk_graph () in
  let added_ids = ref [] in

  let add_node_from_id id =
    if not (List.mem id !added_ids) then (
      added_ids := id :: !added_ids;
      add_node g id
    )
  in

  let add_nodes_from_eq (id, exp) =
    add_node_from_id id;
    List.iter add_node_from_id @@ read_exp (id, exp)
  in

  let process_eq (id, exp) =
    add_nodes_from_eq (id, exp);
    List.iter (add_edge g id) (read_exp (id, exp))
  in

  List.iter process_eq p.p_eqs;
  g


let schedule p =
  let g = programm_to_graph p in
  if has_cycle g then raise Combinational_cycle else

  let sorted_ids = List.rev @@ topological g in

  let rec constr_new_eqs l =
    match l with
    |[] -> []
    |id :: q ->
      try
        let eq = List.find (function eq -> (let (eq_id,_) = eq in eq_id = id)) p.p_eqs in
        eq :: constr_new_eqs q
      with Not_found -> constr_new_eqs q
    in
  
  {
    p_eqs = constr_new_eqs sorted_ids;
    p_inputs = p.p_inputs;
    p_outputs = p.p_outputs;
    p_vars = p.p_vars
  }
