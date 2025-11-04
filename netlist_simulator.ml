open Netlist_ast

type endianism = LittleEndian (* | BigEndian *)

let endianness = LittleEndian

(* let print_only = ref false *)
let number_steps = ref (-1)


let val_to_bool = function
    (* use single-bit values as booleans *)
    |VBit(b) -> b
    |VBitArray(_) -> failwith "Boolean evaluation of buses not defined"

let val_to_int = function
    |VBit(b) -> if b then 1 else 0
    |VBitArray(b_a) ->
        let n = Array.length b_a in
        let sum = ref 0 in
        for i = 0 to n-1 do
            sum := !sum * 2;
            sum := !sum + (if b_a.(
                match endianness with
                |LittleEndian -> n-1 -i
                (* |BigEndian -> i *)
            ) then 1 else 0)
        done;
        !sum

let val_to_bitarray = function
    |VBitArray(arr) -> arr
    |VBit(b) -> [|b|]

let int_to_bitarray n x =
    let b_arr = Array.make n false in
    let xr = ref x in
    for i = 0 to n-1 do
        if !xr mod 2 = 1 then
        b_arr.(
            match endianness with
            |LittleEndian -> i
            (* |BigEndian -> n-1 - i *)
        ) <- true;
        xr := !xr / 2
    done;
    VBitArray(b_arr)

let bitarray_to_string b_arr =
    if b_arr = [||] then "--" else
    Array.fold_left (fun s b -> s^(if b then "1" else "0")) "" b_arr



(* Evaluation of arguments and expressions -> returning values *)

let fetch_id_val env id = Env.find id env

let evaluate_arg env = function
    |Avar(id) -> fetch_id_val env id
    |Aconst(v) -> v

let evaluate_binop env binop a b =
    let ba, bb = 
        val_to_bool @@ evaluate_arg env a, val_to_bool @@ evaluate_arg env b
    in
    match binop with
        |Or -> VBit(ba || bb)
        |Xor ->
            if ba && bb then VBit(false) else VBit(ba || bb)
        |And -> VBit(ba && bb)
        |Nand -> VBit(not (ba && bb))

(* Bus operations *)

let concat_buses a b =
    let a_arr = val_to_bitarray a
    and b_arr = val_to_bitarray b in
    VBitArray(Array.append a_arr b_arr)

let slice_bus i j = function
    |VBitArray(a_arr) when i=j && 0<=i && i< Array.length a_arr ->
        VBit(a_arr.(i))
    |VBitArray(a_arr) when 0<=i && i<=j && j< Array.length a_arr ->
        let c_arr = Array.make (j-i+1) false in
        for k = i to j do
            c_arr.(k-i) <- a_arr.(k)
        done;
        VBitArray(c_arr)
    |VBitArray(_) -> failwith "Slicing out of bounds"
    |_ -> failwith "Slicing only defined for buses"

let select_bus i = function
    |VBitArray(a_arr) when 0<=i && i<Array.length a_arr ->
        VBit(a_arr.(i))
    |VBitArray _ -> failwith "Select out of bounds"
    |_ -> failwith "Select only defined for buses"


(* Memory reading and writing *)

let mem_read mem _ (*addr_size*) word_size read_addr_val =
    let b_arr = Array.make word_size false in
    let read_addr_int = val_to_int read_addr_val in
    for i = 0 to (word_size -1) do
        if mem.(read_addr_int + i) then b_arr.(i) <- true
    done;
    VBitArray(b_arr)

let mem_write mem _ (*addr_size*) write_addr_val data_val =
    let write_addr_int = val_to_int write_addr_val in
    let data = (match data_val with
        |VBit(b) -> [|b|]
        |VBitArray(b_arr) -> b_arr
    ) in
    
    assert (write_addr_int + Array.length data <= Array.length mem);

    for i = 0 to (Array.length data -1) do
        mem.(write_addr_int + i) <- data.(i)
    done


let evaluate_exp mem prev_env env = function
    |Earg(arg) -> evaluate_arg env arg
    |Ereg(id) -> Env.find id prev_env
    |Enot(arg) -> VBit(not (val_to_bool @@ evaluate_arg env arg))
    |Ebinop(binop,a,b) -> evaluate_binop env binop a b
    |Emux(mux,a,b) ->
        if val_to_bool @@ evaluate_arg env mux 
        then evaluate_arg env b else evaluate_arg env a

    |Econcat(arg_a, arg_b) ->
        let a,b = evaluate_arg env arg_a, evaluate_arg env arg_b in
        concat_buses a b
    |Eslice(i, j, arg_a) ->
        slice_bus i j @@ evaluate_arg env arg_a
    |Eselect(i, arg_a) ->
        select_bus i @@ evaluate_arg env arg_a

    |Erom(addr_size, word_size, read_addr)
    |Eram(addr_size, word_size, read_addr, _, _, _) ->
        mem_read mem addr_size word_size (evaluate_arg env read_addr)

let compute_eq mem prev_env env (id, exp) =
    (* Associates the variable's ident with its evaluated expression *)
    Env.add id (
        evaluate_exp mem prev_env env exp
    ) env

let compute_write_eq mem env (_,exp) =
    match exp with
    |Eram(addr_size, _, _, write_enable, write_addr, data)
        when val_to_bool @@ evaluate_arg env write_enable ->
        let write_addr_val = evaluate_arg env write_addr
        and data_val = evaluate_arg env data in
        mem_write mem addr_size write_addr_val data_val
    |_ -> ()




(* User interface *)

let poll_inputs program inputs =
    (* Polls input values one by one : ? ident <- ... *)
    let rec poll env input_id =
        Printf.printf "? %s <- " input_id;
        let input_t = Env.find input_id program.p_vars in
        let scanned_input = read_int_opt () in
        match input_t, scanned_input with
        |TBit, Some(x) when x=1 || x=0 ->
            Env.add input_id (VBit(x=1)) env
        |TBitArray(n), Some(x) when 0 <= x && x < (1 lsl n) ->
            Env.add input_id (int_to_bitarray n x) env
        |_ ->
            Printf.printf "Veuillez fournir une entrée valide\n";
            poll env input_id
    in
    List.fold_left poll Env.empty inputs

let print_outputs env outputs =
    (* Prints outputs (at the end of a cycle) : ident = bool(value) *)
    let print output_id =
        match Env.find output_id env with
        |VBit(b) -> Printf.printf "%s = %s\n" output_id (string_of_bool b)
        |VBitArray(b_arr) ->
            Printf.printf "%s:%d = %s\n"
                output_id
                (Array.length b_arr)
                (bitarray_to_string b_arr)
    in
    List.iter print outputs

(*
let print_all mem env =
    let p_bind (ident, v) =
        match v with
        |VBit(b) -> Printf.printf "%s = %c\n" ident (if b then '1' else '0')
        |VBitArray(b_arr) ->
            Printf.printf "%s:%d = %s\n" ident (Array.length b_arr)
                (bitarray_to_string b_arr)
    in
    List.iter p_bind (Env.bindings env);
    Printf.printf "memory:%d === %s\n" (Array.length mem)
        (bitarray_to_string mem)
*)



let find_req_memory_size program =
    (* returns maximum nomber of bits used to describe addresses *)
    let req_bits = function
        |Erom(addr_size, _, _) -> addr_size
        |Eram(addr_size,_,_,_,_,_) -> addr_size
        |_ -> 0
    in
    program.p_eqs
    |> List.map (fun (_,exp) -> req_bits exp)
    |> List.fold_left (max) 0


let rec compute_cycle program mem prev_env number_steps =
    if number_steps = 0 then () else
    (* print_all mem prev_env; *)
    let input_env = poll_inputs program program.p_inputs in
    let final_env = 
        List.fold_left (compute_eq mem prev_env) input_env program.p_eqs in
    List.iter (compute_write_eq mem final_env) program.p_eqs;
    print_outputs final_env program.p_outputs;
    compute_cycle program mem final_env (number_steps - 1)


let create_initial_env program =
    let set_val_nul env id =
        match Env.find id program.p_vars with
        |TBit -> Env.add id (VBit(false)) env
        |TBitArray(n) -> Env.add id (VBitArray(Array.make n false)) env
    in
    Env.empty
    |> fun env -> List.fold_left set_val_nul env program.p_inputs
    |> fun env -> List.fold_left set_val_nul env (List.map fst program.p_eqs)



let simulator program number_steps =
    (* mem is the memory table, size 2 ^ (max_address_size +1) *)
    let mem = Array.make ( 1 lsl (find_req_memory_size program +1)) false in
    let env = create_initial_env program in
    compute_cycle program mem env number_steps



let compile filename =
  try
    let p = Netlist.read_file filename in
    begin try
        let p = Scheduler.schedule p in
        simulator p !number_steps
      with
        | Scheduler.Combinational_cycle ->
            Format.eprintf "The netlist has a combinatory cycle.@.";
    end;
  with
    | Netlist.Parse_error s -> Format.eprintf "An error accurred: %s@." s; exit 2

let main () =
  Arg.parse
    ["-n", Arg.Set_int number_steps, "Number of steps to simulate"]
    compile
    ""
;;

main ()
