open Netlist_ast

type endianism = LittleEndian (* | BigEndian *)

let endianness = LittleEndian

(* let print_only = ref false *)
let number_steps = ref (-1)


let val_length = function
    |VBit _ -> 1
    |VBitArray(a) -> Array.length a

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

let mem_read t addr_size word_size read_addr_val =
    assert (val_length read_addr_val <= addr_size);

    let read_addr_int = val_to_int read_addr_val in
    if word_size = 1 then VBit(t.(read_addr_int)) else

    let b_arr = Array.make word_size false in
    for i = 0 to (word_size -1) do
        if t.(read_addr_int * word_size + i) then b_arr.(i) <- true
    done;
    VBitArray(b_arr)

let mem_write t addr_size word_size write_addr_val data_val =
    assert (val_length write_addr_val <= addr_size);
    assert (val_length data_val = word_size);

    let write_addr_int = val_to_int write_addr_val in
    if word_size = 1 then 
        t.(write_addr_int) <- val_to_bool data_val
    else

    let data = val_to_bitarray data_val in
    for i = 0 to (word_size -1) do
        t.(write_addr_int * word_size + 1) <- data.(i)
    done


let evaluate_exp mem prev_env env id = function
    |Earg(arg) -> evaluate_arg env arg
    |Ereg(id) -> fetch_id_val prev_env id
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

    |Erom(addr_size, word_size, read_addr) ->
        begin match Hashtbl.find_opt mem id with
        | None -> failwith "No table for ROM"
        | Some(t) -> mem_read t addr_size word_size (evaluate_arg env read_addr)
        end
(*     |Eram(addr_size, word_size ,read_addr, write_enable,_,_) -> *)
    |Eram(addr_size, word_size, read_addr, write_enable, write_addr, data) ->
        let _ = mem_write in
        begin match Hashtbl.find_opt mem id with
        | None -> failwith "No table for RAM"
        | Some(t) -> let out =
            mem_read t addr_size word_size (evaluate_arg env read_addr) in
            if val_to_bool @@ evaluate_arg env write_enable then (
                let write_addr_val = evaluate_arg env write_addr
                and data_val = evaluate_arg env data in
                ignore (write_addr_val); ignore (data_val)
(*                 mem_write t addr_size word_size write_addr_val data_val *)
            );
            out
        end

let compute_eq mem prev_env env (id, exp) =
    (* Associates the variable's ident with its evaluated expression *)
    Env.add id (
        evaluate_exp mem prev_env env id exp
    ) env


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

let print_all mem env =
    let p_bind (ident, v) =
        match v with
        |VBit(b) -> Printf.printf " | %s = %c\n" ident (if b then '1' else '0')
        |VBitArray(b_arr) ->
            Printf.printf " | %s:%d = %s\n" ident (Array.length b_arr)
                (bitarray_to_string b_arr)
    in
    let p_mem id t =
        Printf.printf " | MEM %s:%d == %s\n" 
            id
            (Array.length t)
            (bitarray_to_string t)
    in
    Printf.printf "Print ALL :\n";
    List.iter p_bind (Env.bindings env);
    Printf.printf " |- - MEMORY - -\n";
    Hashtbl.iter p_mem mem



let rec compute_cycle program mem prev_env number_steps =
    if number_steps = 0 then () else
    let input_env = poll_inputs program program.p_inputs in
    print_all mem input_env;
    let final_env =
        List.fold_left (compute_eq mem prev_env) input_env program.p_eqs in
    print_outputs final_env program.p_outputs;
    print_all mem final_env;
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

let create_initial_mem program =
    let mem = Hashtbl.create 17 in
    let is_mem : equation -> bool = function
        | _,Erom(_,_,_) | _,Eram(_,_,_,_,_,_) -> true
        | _ -> false
    in
    let set_val_nul = function
        | id, Erom(addr_size, word_size, _) 
        | id, Eram(addr_size, word_size, _,_,_,_) ->
            Array.make ( (1 lsl addr_size) * word_size ) false
            |> Hashtbl.add mem id
        | _ -> failwith "irrelevant equation"
    in

    List.iter (fun eq -> if is_mem eq then set_val_nul eq) program.p_eqs;
    mem



let simulator program number_steps =
    let mem = create_initial_mem program in
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
