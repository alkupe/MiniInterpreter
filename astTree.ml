(* 
Alex Halter
HPL Spring 14
File astTree.ml
All of the code besides the yacc and lex code is in here.
 *)



(*Type for operators *)
type op = Plus | Sub | Mult | Div


(*All the data structures outlined in the assignment. Closely matches the assignment spec*)
type cmdNode = VarAssign of string * expNode * string  list
        | FieldAssign of expNode * expNode * expNode * string list
        | Skip
        | Sequence of cmdNode * cmdNode * string list
        | While of boolNode * cmdNode * string list
        | If of boolNode * cmdNode * cmdNode * string list
        | Atom of cmdNode * string list
        | Concurrent of cmdNode * cmdNode * string list
        | Call of expNode * expNode * string list
        | Declaration of string * cmdNode * string list
        | Malloc of string * string list
        | Block of cmdNode
        | Empty


and expNode = Variable of string * string list
        | Integer of int
        | Math of op * expNode * expNode * string list
        | Minus of expNode * string list
        | Null
        | FieldLocation of expNode * expNode * string list
        | Procedure of string * cmdNode * string list
        | Field of string * string list


and boolNode = True
        | False
        | Equals of expNode * expNode * string list
        | Lessthan of expNode * expNode * string list


type integer = Int of int

type boolean = Btrue
             | Bfalse
             | Berror

type miniObject = Object of integer

type location = Location of miniObject
                | Nulllocation

type var = Var of string

type environment = Env of var * miniObject

type frame = 
    Decl of environment
  | FCall of environment * stack
and stack =
    frame list

type closure = var * cmdNode * stack
type field = 
    FieldName of string
  | Val

type value =
    Vfield of field
  | Vint of integer
  | VLocation of location
  | Clo of closure

type taintedvalue =
    Value of value
  | TError

type heapEntry = HeapEntry of (field * taintedvalue ref) list ref

type heapType = heapEntry list

type conf = Conf of cmdNode * stack * heapType ref

(*returns the primitive (int) location on the heap of a given variable *)
let rec get_heap_location id stack =
    match stack with
    hd::tl -> ( match hd with 
                Decl(Env(Var(varid),Object(Int(pos)))) -> if id = varid then pos else get_heap_location id tl
                | FCall(Env(Var(varid),Object(Int(pos))),newstack) -> if id = varid then pos else get_heap_location id tl

                )
    | [] -> failwith ("heap location error")


(* Function returns the value of a variable. Note that if the variable is not malloced, it will return the value held in the reserved Val field.
    If it is a malloced variable, it just returns the object itself--the heap location in its entirely
    Note that heap values for a variable will have one of two states: either it has a single Val entry (and is unmalloced)
    or it has zero or more field entries. 

 *)
let get_value heapVal loc =
    let rec check_all hv = 
    match hv with 
        hd::tl -> 
                ( match hd with 
                    (* If the hd is a Val posiition it is unmalloced, otherwise it is a malloced object *)
                    Val,tv_ref ->     (match !tv_ref with Value(v) -> Value(v)
                                    | TError -> failwith "Error getting value: heap value error"
                                    )

                    | FieldName(name),_ -> Value(VLocation(Location(Object(Int(loc)))))
                                    
                )
        (* if the heap entry is empty, then it just hasn't been assigned anything yet *)
        | [] -> Value(VLocation(Location(Object(Int(loc)))))
    in 
    match heapVal with
    HeapEntry e -> check_all !e


(* Helper function sets the reserved Value position of a variable on the heap *)
let set_value heapVal toSet =
    let rec set_val hv = 
    match hv with 
        hd::tl -> 
                ( match hd with 
                  
                    Val,tv_ref -> (match !tv_ref with Value(v) -> 
                                      (match toSet with Value(v) -> tv_ref := Value(v)
                                        | TError -> failwith "Error setting value: heap value error"
                                        ) 
                                    | TError -> failwith "Error setting value: heap value error"
                                  )
                    | _,_ -> set_val tl
                                    
                )
        | [] -> failwith "Error setting value: setting the value of a malloced variable"
    in 
    match heapVal with
    HeapEntry e -> set_val !e


(* Sets the reserved Value position of a variable on the heap, first it iterates to the right position then calls the set_value helper function *)
let rec set_heap_value myheap loc toSet =
    match myheap with 
    hd::tl -> if loc = 0 then set_value hd toSet else set_heap_value tl (loc-1) toSet
    |[] -> failwith "Error setting heap value: Location doesn't exist"


(* Helper function to set a heap field to a value. Note that a field can either exist and need to mutated or not exist yet but should be vivified*)
let set_field heapVal field value heap=
    let rec set_field_helper hv fieldname hvref= 
        match hv with 
            hd::tl -> 
                    ( match hd with 
                      
                        Val,tv_ref -> failwith "Error: setting a heap field of an unmalloced variable"
                        | FieldName(name),tv_ref -> if name = fieldname then   (tv_ref := value ) else set_field_helper tl fieldname hvref
                                        
                    )
            | [] ->  hvref := (FieldName(fieldname),ref value)::!hvref;heap := !heap @ [HeapEntry(hvref)];()
        in 
        (match heapVal with
        HeapEntry e -> (match field with 
                        Value(Vfield(FieldName(name))) -> set_field_helper !e name e
                        | _ -> failwith "Error :Setting a heap field of a nonfield value"
                        )
        )

(* Function to set the heap field of a variable, first by iterating to the right heap position, then calling the helper function to set the field *)
let rec  set_heap_field pos field value myheap= 
   let rec iterateHeap pos field value heapref heap = 
   (match heap with
    hd::tl -> if pos = 0 then set_field hd field value heapref else iterateHeap (pos-1) field value heapref tl
    | [] -> failwith "Error setting field: heap position doesn't exist")
    in iterateHeap pos field value myheap !myheap


(* Prints the different tained values *)
let print_value value =
    match value with
    Value(Vint(Int(myval))) -> print_int myval; print_string "\n"; flush stdout
    |  Value(Clo(Var(id),n1,stack)) -> print_string ("procedure with parameter " ^ id ^ "\n"); flush stdout
    | Value(Vfield(FieldName(name))) -> print_string ("Field: " ^ name ^"\n");flush stdout
    | Value(Vfield(Val)) -> print_string ("Value: this shouldn't happen as values should be dereferenced\n");flush stdout
    | Value(VLocation(Location(Object(Int(pos))))) -> print_string ("Variable: ")
    | Value (VLocation Nulllocation) -> print_string "Null value\n";flush stdout
    | TError -> print_string "Error Value\n";flush stdout

(* Prints the entire heap at a given position *)
let rec print_heap_fields heapValue =
    let rec printField hv = 
    match hv with 
        hd::tl -> 
                ( match hd with 
                  
                    Val,tv_ref -> 
                                    print_string "value = "; print_value !tv_ref

                    | FieldName(name),tv_ref -> 
                                                print_string ("field name " ^ name ^ " = "); print_value !tv_ref;
                                                printField tl
                                    
                )
        | [] -> ()
    in 
    match heapValue with
    HeapEntry e -> printField !e

(* Iterates to the right slot on the heap then calls the print function *)
let rec print_heap loc myheap=
    match myheap with 
    hd::tl -> if loc = 0 then print_heap_fields hd else print_heap (loc-1) tl 
    |[] -> failwith "Error printing value"


(* Prints the entire stack and the current values for each frame on the stack *)
let rec print_stack stack heap =
    match stack with
    hd::tl -> ( match hd with 
                Decl(Env(Var(id) ,  Object(Int(loc)))) -> print_string ("Printing heap for declaration " ^ id ^ " in position ");print_int loc;print_string "\n";
                 print_heap loc heap;print_stack tl heap
                | FCall(Env(Var(id) ,  Object(Int(loc))),newstack) -> print_string ("Printing heap for function call " ^ id ^ "\n");
                 print_heap loc heap;print_stack tl heap
                )
    | [] -> ()


(* Restores the stack to its previous state after a function call, and pops the stack for a declaration *)
let rec pop_or_restore stack =
    match stack with 
    hd::tl -> (match hd with
                Decl(Env(Var(varid),Object(Int(pos)))) -> tl
                | FCall(Env(Var(varid),Object(Int(pos))),newstack) ->newstack

                ) 
    | [] -> failwith "Stack failure"



(* Helper function to get the value held at a field. Note that either we return the current value at a field (if it had already been used and assigned to
   or if it hasn't been used yet, the null value is there. 

*)
let rec get_field heapValue field =
    let rec get_field_helper hv name= 
    match hv with 
        hd::tl -> 
                ( match hd with 
                  
                    Val,tv_ref -> failwith "Error looking up heap field of an unmalloced variable"
                    | FieldName(matchname),tv_ref -> if name = matchname then (match !tv_ref with Value(v) -> Value(v)
                                                                                                    | TError -> TError
                                                                                ) else get_field_helper tl name
                                    
                )
        | [] -> Value(VLocation(Nulllocation))
    in 
    match field with
    FieldName(name) -> ( match heapValue with
                        HeapEntry e 
                        -> get_field_helper !e name
                       )
    | Val -> failwith "Error looking up heap field of an unmalloced variable"

(* Iterates to the right position on the heap then calls the helper function to get the field there *)
let rec  get_heap_field pos field  myheap= 
   match myheap with
    hd::tl -> if pos = 0 then get_field hd field else get_heap_field (pos-1) field tl
    | [] -> failwith "Error getting value:heap position doesn't exist"

(* Getter for the reserved Val field on the heap *)
let get_heap_value loc myheap=
    let rec get_heap_value_helper loc pos myheap = 
    match myheap with 
    hd::tl -> if pos = 0 then get_value hd loc else get_heap_value_helper loc (pos-1) tl
    |[] -> TError
    in
    get_heap_value_helper loc loc myheap


 (* Evaluation function for expressions, follows assignment specs closely*)
 let rec eval_expr exp stack heap=
    match exp with
    Variable(id,l) ->  let heaploc = get_heap_location id stack in
                        get_heap_value heaploc !heap
    | Procedure(id,n1,l) -> Value(Clo(Var(id),n1,stack))
    | Integer(value) -> Value(Vint(Int(value)))
    | Math(op,n1,n2,l) -> do_math_op op n1 n2 stack heap
    | Minus(n1,l) -> let v1 = eval_expr n1 stack heap in
                        (match v1 with Value(Vint(Int(value1))) -> Value(Vint(Int(-value1)))

                         | _ -> TError)
    | Null -> Value(VLocation(Nulllocation))
    | FieldLocation(n1,n2,l) -> let e1 = eval_expr n1 stack heap
                                         and e2 = eval_expr n2 stack heap
                                        in
                                        (match e1,e2 with
                                            Value(VLocation(Location(Object(Int(pos))))), Value(Vfield(vfield))-> 
                                            get_heap_field pos vfield !heap
                                         | _,_ ->  failwith "Error getting field location: type error"
                                    )
    | Field(id,l) -> Value(Vfield(FieldName(id)))
and
    do_math_op op n1 n2 stack heap =
    match op with
    Sub -> let v1 = eval_expr n1 stack heap
            and v2 = eval_expr n2 stack heap
            in (match v1,v2 with
                Value(Vint(Int(value1))),Value(Vint(Int(value2))) ->  Value(Vint(Int(value1 - value2)))
                |_,_ -> TError )
    |Plus -> let v1 = eval_expr n1 stack heap
            and v2 = eval_expr n2 stack heap
            in (match v1,v2 with
                Value(Vint(Int(value1))),Value(Vint(Int(value2))) ->  Value(Vint(Int(value1 + value2)))
                |_,_ -> TError )
    |Mult -> let v1 = eval_expr n1 stack heap
            and v2 = eval_expr n2 stack heap
            in (match v1,v2 with
                Value(Vint(Int(value1))),Value(Vint(Int(value2))) ->  Value(Vint(Int(value1 * value2)))
                |_,_ -> TError )
    |Div -> let v1 = eval_expr n1 stack heap
            and v2 = eval_expr n2 stack heap
            in (match v1,v2 with
                Value(Vint(Int(value1))),Value(Vint(Int(value2))) ->  Value(Vint(Int(value1 / value2)))
                |_,_ -> TError )

(* Boolean evaluation function, according to spec*)
 let rec eval_bool bool stack heap = 
    match bool with 
    True -> Btrue
    | False -> Bfalse
    | Equals (e1,e2,l) -> let v1 = eval_expr e1 stack heap
                          and v2 = eval_expr e2 stack heap
                          in (match v1,v2 with
                             Value(Vint(Int(value1))),Value(Vint(Int(value2))) -> if value1 = value2 then Btrue else Bfalse
                             | _,_ -> Berror
                          )
     | Lessthan (e1,e2,l) -> let v1 = eval_expr e1 stack heap
                            and v2 = eval_expr e2 stack heap
                            in (match v1,v2 with
                             Value(Vint(Int(value1))),Value(Vint(Int(value2))) -> if value1 < value2 then Btrue else Bfalse
                             | _,_ -> Berror
                          )


(* Prints the operator for math operations *)
let print_op op =
    match op with
    Plus -> print_string " + "
    | Sub -> print_string " - "
    | Mult -> print_string " * "
    | Div -> print_string " / "


(* Changes the heap value for a given slot to a malloced state *)
let gen_new_in_heap pos heap= 
    let rec genNew myheap pos = 
    (match myheap with
    hd::tl -> if pos = 0 then HeapEntry(ref[])::tl else hd::genNew tl (pos-1)
    | [] -> []
    )  
    in heap := genNew !heap pos


(* Mutually recursive functions to print the tree. Walks the entire AST and prints each node *)
 let rec print_tree n = 
  (match n with
      Declaration(id,n1,l) -> print_string ("var " ^ id ^ " ;");print_tree n1; flush stdout;()
    | VarAssign(id,n1,l) -> print_string (id ^ " = ");print_expr n1; flush stdout;()
    | FieldAssign(n1,n2,n3,l) -> print_expr n1; print_string "."; print_expr n2; print_string " = ";print_expr n3; flush stdout;()
    | Skip ->print_string "skip";()
    | Sequence(n1,n2,l) -> print_string "{";print_tree n1;print_string " ; ";print_tree n2 ;print_string "}"; flush stdout;()
    | While(n1,n2,l) -> print_string "while ";print_bool n1 ;print_string " " ;print_tree n2 ;flush stdout;()
    | If(n1,n2,n3,l) -> print_string "if ";print_bool n1 ; print_string " then "; print_tree n2 ;print_string " else "; print_tree n3 ; flush stdout;()
    | Atom(n1,l) -> print_string "atom(";print_tree n1 ;print_string") "; flush stdout;()
    | Concurrent(n1,n2,l) -> print_string "{";print_tree n1 ;print_string " ||| ";print_tree n2 ;print_string"}"; flush stdout;()
    | Call(n1,n2,l) -> print_expr n1 ;print_string"(";print_expr n2 ;print_string") "; flush stdout;()
    | Malloc(id,l) -> print_string "malloc(";print_string id;print_string")"; flush stdout;() 
    | Block(n1) -> print_string "Block(";print_tree n1;print_string")"; flush stdout;() 
    | Empty -> ()
    )
and print_expr expr = 
 (match expr with
   Variable(id,l) -> print_string id;flush stdout;()
    | Procedure(id,n1,l) -> print_string ("proc " ^ id ^ ":"); print_tree n1;flush stdout;()
    | Integer(value) -> print_int value;flush stdout;()
    | Math(op,n1,n2,l) -> print_expr n1;print_op op ;print_expr n2 ;flush stdout;()
    | Minus(n1,l) -> print_string " - " ; print_expr n1;flush stdout;()
    | Null -> print_string " null ";
    | FieldLocation(n1,n2,l) -> print_expr n1; print_string ".";print_expr n2 ;()
    | Field(id,l) -> print_string id;flush stdout;()
 )

and print_bool b =
(match b with
	True -> print_string " true ";flush stdout;()
    | False -> print_string " false ";flush stdout;()
    | Equals(n1,n2,l) -> print_expr n1; print_string " == ";print_expr n2 ; flush stdout;()
    | Lessthan(n1,n2,l) ->  print_expr n1; print_string " < ";print_expr n2 ; flush stdout;()
)


(* Debug function to print scopes *)
let print_scope s =
    print_string "Printing Current Scope:\n";
    let rec ps s =
    match s with
    hd::tl -> print_string hd; print_string "\n";flush stdout; ps tl
    | [] -> ()
in 
    ps s


(* Recursive functions to decorate the AST with the declared variables in the scope. Fails if the static scope rules are violated, as specified on pages 3-4 *)
 let rec decorate_tree n scope= 
  (match n with
      Declaration(id,n1,l) -> Declaration(id,(decorate_tree n1 (id::scope)),scope)
    | VarAssign(id,n1,l) -> if not (List.mem id scope) then  failwith "Scope check error:variable not declared"; VarAssign(id,decorate_exp n1 scope,scope)
    | FieldAssign(n1,n2,n3,l) -> FieldAssign((decorate_exp n1 scope),(decorate_exp n2 scope),(decorate_exp n3 scope),scope) 
    | Skip -> n
    | Sequence(n1,n2,l) -> Sequence ((decorate_tree n1 scope) ,(decorate_tree n2 scope) ,scope)
    | While(n1,n2,l) -> While((decorate_bool n1 scope),(decorate_tree n2 scope),scope)
    | If(n1,n2,n3,l) -> If ((decorate_bool n1 scope),(decorate_tree n2 scope),(decorate_tree n3 scope),scope)
    | Atom(n1,l) -> Atom((decorate_tree n1 scope),scope)
    | Concurrent(n1,n2,l) ->  Concurrent ((decorate_tree n1 scope),(decorate_tree n2 scope),scope)
    | Call(n1,n2,l) -> Call ((decorate_exp n1 scope),(decorate_exp n2 scope),scope)
    | Malloc(id,l) -> if not (List.mem id scope) then failwith "Scope check error: variable not declared" ;n
    | Block (n1)-> Block(decorate_tree n1 scope)
    | Empty -> n
)
and decorate_exp expr scope= 
 (match expr with
   Variable(id,l) -> if not (List.mem id scope) then failwith "Scope check error: variable not declared" ;expr
    | Procedure(id,n1,l) -> Procedure (id,(decorate_tree n1 (id::scope)),scope)
    | Math(op,n1,n2,l) -> Math (op ,(decorate_exp n1 scope),(decorate_exp n2 scope),scope)
    | Integer(value) -> expr
    | Minus(n1,l) -> Minus ((decorate_exp n1 scope) ,scope)
    | Null -> expr
    | FieldLocation(n1,n2,l) -> FieldLocation ((decorate_exp n1 scope),(decorate_exp n2 scope),scope)
    | Field (id,l) -> expr
 )

and decorate_bool b scope =
(match b with
	True -> b
    | False ->  b
    | Equals(n1,n2,l) -> Equals ((decorate_exp n1 scope),(decorate_exp n2 scope),scope)
    | Lessthan(n1,n2,l) -> Lessthan ((decorate_exp n1 scope),(decorate_exp n2 scope),scope)
)

(* Function to process each node of the tree, iterating through each command type, according to the spec on small-step operational semantics *)
let rec process_tree config=
    (match config with
    Conf(command,stack,heap) ->
        (match command with
            (*If we reach empty here, we're done and return the empty configuration *)
            Empty -> Conf(Empty,stack,heap)

            (*Iterate through the blocks we've already processed, then when we reach the current block, when it returns Empty, restore/pop the stack*)
            | Block(n1) -> let nextCommand = process_tree (Conf(n1,stack,heap)) in
                           (match nextCommand with
                            Conf(Empty,newstack,newheap) -> Conf(Empty,(pop_or_restore newstack),newheap) 
                            | Conf(comm,newstack,newheap) -> Conf(Block comm,newstack,newheap)
                            )
            (* When a variable is declared, put it on the spot with the null value in the Val field, add it the stack as a Block*)           
            |Declaration(id,n1,l) -> let myframe = Decl(Env(Var(id) ,  Object(Int(List.length !heap)))) 
                                    in heap := !heap @ [HeapEntry(ref[Val , ref (Value(VLocation(Nulllocation)))])];
                                    Conf(Block n1,myframe::stack,heap)
            (* Straightforward assignment to a variable*)                   
            | VarAssign(id,n1,l) ->  let toSet = eval_expr n1 stack heap
                                  and heaploc = get_heap_location id stack
                                  in set_heap_value !heap heaploc toSet;
                                  Conf(Empty,stack,heap)
            (* Assignment to a field location. argument 1 must be an object on the heap, and argument 2 must be a field name *)                          
            | FieldAssign(n1,n2,n3,l) -> let e1 = eval_expr n1 stack heap
                                         and e2 = eval_expr n2 stack heap
                                         and e3 = eval_expr n3 stack heap
                                        in
                                        (match e1,e2 with
                                            Value(VLocation(Location(Object(Int(pos))))), Value(Vfield(vfield))-> 
                                            set_heap_field pos (Value(Vfield(vfield))) e3 heap ;
                                            Conf(Empty,stack,heap)
                                         | _,_ ->  failwith "Assigning a field to a variable that hasn't been malloced"
                                    )
            | Skip -> Conf(Empty,stack,heap)

            (* Per the spec, execute a comannd in the first command of the sequence, then if it is complete, return the second command 
            Else return a sequence of the next command of the first command, in the same sequence*)
            | Sequence(n1,n2,l) -> let nextCommand = process_tree (Conf(n1,stack,heap))
                                   in

                                   (match nextCommand with
                                    Conf(myblock,newstack,newheap) -> 
                                    (match myblock with 
                                    Empty -> Conf(n2, newstack,heap)
                                    | comm -> Conf(Sequence(comm,n2,l),newstack,newheap)
                                    ))
            (* Per the spec if boolean is false, return Empty. If the boolean is true, return a sequence of the body of the while followed by the same while command*)
            | While(n1,n2,l) -> let eb = eval_bool n1 stack heap
                                in (match eb with
                                    Btrue -> Conf(Sequence(n2,While(n1,n2,l),l),stack,heap)
                                    | Bfalse -> Conf(Empty,stack,heap)
                                    | Berror -> failwith "Boolean type error"
                                    ) 
            (* Per the spec, if the boolean is true return the first command, if the boolean is false return the second command *)
            | If(n1,n2,n3,l) -> let eb = eval_bool n1 stack heap
                                in (match eb with
                                Btrue -> Conf(n2,stack,heap)
                                | Bfalse -> Conf(n3,stack,heap)
                                | Berror -> failwith "Boolean type error"
                                )
            (* The key with atomic commands is to keep control inside an atomic command, ensuring that control can't return to a potential calling concurrent command *)
            | Atom(n1,l) -> let nextCommand = process_tree (Conf(n1,stack,heap))
                            in
                            (match nextCommand with
                            Conf(myblock,newstack,newheap) -> 
                                (match myblock with 
                                Empty -> Conf(Empty,stack,heap)
                                | comm -> Conf(Atom(myblock,l),newstack,newheap)
                                ))
            (* As long as both commands are not comlete, each time flip a coin and exit one or the other command, then return a concurrent command of the next command and other command*)
            | Concurrent(n1,n2,l) ->  ( match Random.bool () with
                                        true -> 
                                          let nextCommand = process_tree (Conf(n1,stack,heap)) in
                                          (match nextCommand with
                                          Conf(myblock,newstack,newheap) -> 
                                            (match myblock with 
                                            Empty -> Conf(n2,stack,heap)
                                            | comm -> Conf(Concurrent(comm,n2,l),newstack,newheap)
                                            ))
                                      | false ->
                                          let nextCommand = process_tree (Conf(n2,stack,heap)) in
                                          (match nextCommand with
                                          Conf(myblock,newstack,newheap) -> 
                                            (match myblock with 
                                            Empty -> Conf(n1,stack,heap)
                                            | comm -> Conf(Concurrent(n1,comm,l),newstack,newheap)
                                            )))
            (* Put a new call frame on the stack, with the value of the second expression assigned the paramteter in the stack of the function.
                the stack of the procedure declaration is used. Note that if the first expression is not function (closure) then it errors out.
            *)
            | Call(n1,n2,l) -> let e1 = eval_expr n1 stack heap and
                               e2 = eval_expr n2 stack heap
                                in
                                (match e1 with
                                    Value(Clo(Var(param),body,decstack)) -> let myframe = FCall((Env(Var(param) ,  Object(Int(List.length !heap)))),stack) 
                                                                             in heap := !heap @ [HeapEntry(ref[Val , ref (e2)])];
                                                                             Conf(Block(body),myframe::decstack,heap)
                                    | _ -> failwith "Calling a function that isn't a function"  
                                )
             (*Change the heap value of the variable to a malloced type*)                    
            | Malloc(id,l) -> let pos = get_heap_location id stack in
                              gen_new_in_heap pos heap;
                              Conf(Empty,stack,heap)
            )
        )
(* Control function for executing the sequence of commands. Executes a command, then prints some information about the current command and state of stack and heap*)
and process_control config =
    let next = process_tree config
        in 
    (match next with
    Conf(myblock,stack,heap) -> 
        (match myblock with 
        Empty -> 
            print_string "****************************\n";
            print_newline ();
            print_stack stack !heap; (* this shouldn't print anything *)
            print_newline ();
            print_string "Program Terminates\n";
            flush stdout;
        | comm -> 
            print_string "**************Stack and heap dump**************\n";
            print_newline ();
            print_stack stack !heap;
            print_newline ();
            flush stdout;
            print_string "\nNext Command\n";
            print_tree comm;
            print_newline ();
            flush stdout;
            process_control next
        )
    )


(* Called from the YACC at the top level program entry point, once all the parsing is complete, entry to the AstTree code *)
let run tree =
    print_string "**************Program Starting**************\n";
    print_tree tree;
    print_newline ();
    process_control (Conf((decorate_tree tree []),[], ref([] : heapType)))