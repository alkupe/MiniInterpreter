
type op = Plus | Sub | Mult | Div

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


let rec getHeapLocation id stack =
    match stack with
    hd::tl -> ( match hd with 
                Decl(Env(Var(varid),Object(Int(pos)))) -> if id = varid then pos else getHeapLocation id tl
                | FCall(Env(Var(varid),Object(Int(pos))),newstack) -> if id = varid then pos else getHeapLocation id tl

                )
    | [] -> failwith ("heap location error")


(* Function returns the value of a variable. Note that if the variable is not malloced, it will return the value held in the reserved Val field.
    If it is a malloced variable, it just returns the object itself--the heap location in its entirely
    Note that heap values for a variable will have one of two states: either it has a single Val entry (and is unmalloced)
    or it has zero or more field entries. 

 *)
let getValue heapVal loc =
    let rec checkAll hv = 
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
    HeapEntry e -> checkAll !e

let setValue heapVal toSet =
    let rec setVal hv = 
    match hv with 
        hd::tl -> 
                ( match hd with 
                  
                    Val,tv_ref -> (match !tv_ref with Value(v) -> 
                                      (match toSet with Value(v) -> tv_ref := Value(v)
                                        | TError -> failwith "Error setting value: heap value error"
                                        ) 
                                    | TError -> failwith "Error setting value: heap value error"
                                  )
                    | _,_ -> setVal tl
                                    
                )
        | [] -> failwith "Error setting value: setting the value of a malloced variable"
    in 
    match heapVal with
    HeapEntry e -> setVal !e



let rec setHeapValue myheap loc toSet =
    match myheap with 
    hd::tl -> if loc = 0 then setValue hd toSet else setHeapValue tl (loc-1) toSet
    |[] -> failwith "Error setting heap value: Location doesn't exist"



let setField heapVal field value heap=
    let rec setFieldHelper hv fieldname hvref= 
        match hv with 
            hd::tl -> 
                    ( match hd with 
                      
                        Val,tv_ref -> failwith "Error: setting a heap field of an unmalloced variable"
                        | FieldName(name),tv_ref -> if name = fieldname then   (tv_ref := value ) else setFieldHelper tl fieldname hvref
                                        
                    )
            | [] ->  hvref := (FieldName(fieldname),ref value)::!hvref;heap := !heap @ [HeapEntry(hvref)];()
        in 
        (match heapVal with
        HeapEntry e -> (match field with 
                        Value(Vfield(FieldName(name))) -> setFieldHelper !e name e
                        | _ -> failwith "Error :Setting a heap field of a nonfield value"
                        )
        )

let print_value value =
    match value with
    Value(Vint(Int(myval))) -> print_int myval; print_string "\n"; flush stdout
    |  Value(Clo(Var(id),n1,stack)) -> print_string ("procedure with parameter " ^ id ^ "\n"); flush stdout
    | Value(Vfield(FieldName(name))) -> print_string ("Field: " ^ name ^"\n");flush stdout
    | Value(Vfield(Val)) -> print_string ("Value: this shouldn't happen as values should be dereferenced\n");flush stdout
    | Value(VLocation(Location(Object(Int(pos))))) -> print_string ("Variable: ")
    | Value (VLocation Nulllocation) -> print_string "Null value\n";flush stdout
    | TError -> print_string "Error Value\n";flush stdout

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

let rec print_heap loc myheap=
    match myheap with 
    hd::tl -> if loc = 0 then print_heap_fields hd else print_heap (loc-1) tl 
    |[] -> failwith "Error printing value"

let rec print_stack stack heap =
    match stack with
    hd::tl -> ( match hd with 
                Decl(Env(Var(id) ,  Object(Int(loc)))) -> print_string ("Printing heap for declaration " ^ id ^ "\n");
                 print_heap loc heap;print_stack tl heap
                | FCall(Env(Var(id) ,  Object(Int(loc))),newstack) -> print_string ("Printing heap for function call " ^ id ^ "\n");
                 print_heap loc heap;print_stack tl heap
                )
    | [] -> ()



let rec check_and_restore stack =
    match stack with 
    hd::tl -> (match hd with
                Decl(Env(Var(varid),Object(Int(pos)))) -> tl
                | FCall(Env(Var(varid),Object(Int(pos))),newstack) ->newstack

                ) 
    | [] -> failwith "Stack failure"




let rec getField heapValue field =
    let rec getFieldHelper hv name= 
    match hv with 
        hd::tl -> 
                ( match hd with 
                  
                    Val,tv_ref -> failwith "Error looking up heap field of an unmalloced variable"
                    | FieldName(matchname),tv_ref -> if name = matchname then (match !tv_ref with Value(v) -> Value(v)
                                                                                                    | TError -> failwith "fail"
                                                                                ) else getFieldHelper tl name
                                    
                )
        | [] -> Value(VLocation(Nulllocation))
    in 
    match field with
    FieldName(name) -> ( match heapValue with
                        HeapEntry e 
                        -> getFieldHelper !e name
                       )
    | Val -> failwith "Error looking up heap field of an unmalloced variable"


let rec  getHeapField pos field  myheap= 
   match myheap with
    hd::tl -> if pos = 0 then getField hd field else getHeapField (pos-1) field tl
    | [] -> failwith "Error getting value:heap position doesn't exist"


let rec  setHeapField pos field value myheap= 
   let rec iterateHeap pos field value heapref heap =   
   (match heap with
    hd::tl -> if pos = 0 then setField hd field value heapref else iterateHeap (pos-1) field value heapref tl
    | [] -> failwith "Error setting field: heap position doesn't exist")
    in iterateHeap pos field value myheap !myheap


let rec getHeapValue loc myheap=
    let copy = loc in
    match myheap with 
    hd::tl -> if loc = 0 then getValue hd copy else getHeapValue (loc-1) tl
    |[] -> TError

 let rec evalexp exp stack heap=
    match exp with
    Variable(id,l) ->  let heaploc = getHeapLocation id stack in
                        getHeapValue heaploc !heap
    | Procedure(id,n1,l) -> Value(Clo(Var(id),n1,stack))
    | Integer(value) -> Value(Vint(Int(value)))
    | Math(op,n1,n2,l) -> doMath op n1 n2 stack heap
    | Minus(n1,l) -> let v1 = evalexp n1 stack heap in
                        (match v1 with Value(Vint(Int(value1))) -> Value(Vint(Int(-value1)))

                         | _ -> TError)
    | Null -> Value(VLocation(Nulllocation))
    | FieldLocation(n1,n2,l) -> let e1 = evalexp n1 stack heap
                                         and e2 = evalexp n2 stack heap
                                        in
                                        (match e1,e2 with
                                            Value(VLocation(Location(Object(Int(pos))))), Value(Vfield(vfield))-> 
                                            getHeapField pos vfield !heap
                                         | _,_ ->  failwith "Error getting field location: type error"
                                    )
    | Field(id,l) -> Value(Vfield(FieldName(id)))
and
    doMath op n1 n2 stack heap =
    match op with
    Sub -> let v1 = evalexp n1 stack heap
            and v2 = evalexp n2 stack heap
            in (match v1,v2 with
                Value(Vint(Int(value1))),Value(Vint(Int(value2))) ->  Value(Vint(Int(value1 - value2)))
                |_,_ -> TError )
    |Plus -> let v1 = evalexp n1 stack heap
            and v2 = evalexp n2 stack heap
            in (match v1,v2 with
                Value(Vint(Int(value1))),Value(Vint(Int(value2))) ->  Value(Vint(Int(value1 + value2)))
                |_,_ -> TError )
    |Mult -> let v1 = evalexp n1 stack heap
            and v2 = evalexp n2 stack heap
            in (match v1,v2 with
                Value(Vint(Int(value1))),Value(Vint(Int(value2))) ->  Value(Vint(Int(value1 * value2)))
                |_,_ -> TError )
    |Div -> let v1 = evalexp n1 stack heap
            and v2 = evalexp n2 stack heap
            in (match v1,v2 with
                Value(Vint(Int(value1))),Value(Vint(Int(value2))) ->  Value(Vint(Int(value1 / value2)))
                |_,_ -> TError )

 let rec evalbool bool stack heap = 
    match bool with 
    True -> Btrue
    | False -> Bfalse
    | Equals (e1,e2,l) -> let v1 = evalexp e1 stack heap
                          and v2 = evalexp e2 stack heap
                          in (match v1,v2 with
                             Value(Vint(Int(value1))),Value(Vint(Int(value2))) -> if value1 = value2 then Btrue else Bfalse
                             | _,_ -> Berror
                          )
     | Lessthan (e1,e2,l) -> let v1 = evalexp e1 stack heap
                            and v2 = evalexp e2 stack heap
                            in (match v1,v2 with
                             Value(Vint(Int(value1))),Value(Vint(Int(value2))) -> if value1 < value2 then Btrue else Bfalse
                             | _,_ -> Berror
                          )



let print_op op =
    match op with
    Plus -> print_string " + "
    | Sub -> print_string " - "
    | Mult -> print_string " * "
    | Div -> print_string " / "


let genNewInHeap pos heap= 
    let rec genNew myheap pos = 
    (match myheap with
    hd::tl -> if pos = 0 then HeapEntry(ref[])::tl else hd::genNew tl (pos-1)
    | [] -> []
    )  
    in heap := genNew !heap pos

 let rec print_tree n = 
  (match n with
      Declaration(id,n1,l) -> print_string ("var " ^ id ^ " ;");print_tree n1; flush stdout;()
    | VarAssign(id,n1,l) -> print_string (id ^ " = ");print_exp n1; flush stdout;()
    | FieldAssign(n1,n2,n3,l) -> print_exp n1; print_string "."; print_exp n2; print_string " = ";print_exp n3; flush stdout;()
    | Skip ->print_string "skip";()
    | Sequence(n1,n2,l) -> print_string "{";print_tree n1;print_string " ; ";print_tree n2 ;print_string "}"; flush stdout;()
    | While(n1,n2,l) -> print_string "while ";print_bool n1 ;print_tree n2 ;flush stdout;()
    | If(n1,n2,n3,l) -> print_string "if ";print_bool n1 ; print_string " then "; print_tree n2 ;print_string " else "; print_tree n3 ; flush stdout;()
    | Atom(n1,l) -> print_string "atom(";print_tree n1 ;print_string") "; flush stdout;()
    | Concurrent(n1,n2,l) -> print_string "{";print_tree n1 ;print_string " ||| ";print_tree n2 ;print_string"}"; flush stdout;()
    | Call(n1,n2,l) -> print_exp n1 ;print_string"(";print_exp n2 ;print_string") "; flush stdout;()
    | Malloc(id,l) -> print_string "malloc(";print_string id;print_string")"; flush stdout;() 
    | Block(n1) -> print_string "Block<";print_tree n1;print_string">"; flush stdout;() 
    | Empty -> ()
    )
and print_exp e = 
 (match e with
   Variable(id,l) -> print_string id;flush stdout;()
    | Procedure(id,n1,l) -> print_string ("proc " ^ id ^ ":"); print_tree n1;flush stdout;()
    | Integer(value) -> print_int value;flush stdout;()
    | Math(op,n1,n2,l) -> print_exp n1;print_op op ;print_exp n2 ;flush stdout;()
    | Minus(n1,l) -> print_string " - " ; print_exp n1;flush stdout;()
    | Null -> print_string " null ";
    | FieldLocation(n1,n2,l) -> print_exp n1; print_string ".";print_exp n2 ;()
    | Field(id,l) -> print_string id;flush stdout;()
 )

and print_bool b =
(match b with
	True -> print_string " true ";flush stdout;()
    | False -> print_string " false ";flush stdout;()
    | Equals(n1,n2,l) -> print_exp n1; print_string " == ";print_exp n2 ; flush stdout;()
    | Lessthan(n1,n2,l) ->  print_exp n1; print_string " == ";print_exp n2 ; flush stdout;()
)

let print_scope s =
    print_string "Printing Current Scope:\n";
    let rec ps s =
    match s with
    hd::tl -> print_string hd; print_string "\n";flush stdout; ps tl
    | [] -> ()
in 
    ps s

 let rec decorate_tree n start= 
  (match n with
      Declaration(id,n1,l) -> Declaration(id,(decorate_tree n1 (id::start)),start)
    | VarAssign(id,n1,l) -> if not (List.mem id start) then  failwith "Scope check error:variable not declared"; VarAssign(id,decorate_exp n1 start,start)
    | FieldAssign(n1,n2,n3,l) -> FieldAssign((decorate_exp n1 start),(decorate_exp n2 start),(decorate_exp n3 start),start) 
    | Skip -> n
    | Sequence(n1,n2,l) -> Sequence ((decorate_tree n1 start) ,(decorate_tree n2 start) ,start)
    | While(n1,n2,l) -> While((decorate_bool n1 start),(decorate_tree n2 start),start)
    | If(n1,n2,n3,l) -> If ((decorate_bool n1 start),(decorate_tree n2 start),(decorate_tree n3 start),start)
    | Atom(n1,l) -> Atom((decorate_tree n1 start),start)
    | Concurrent(n1,n2,l) ->  Concurrent ((decorate_tree n1 start),(decorate_tree n2 start),start)
    | Call(n1,n2,l) -> Call ((decorate_exp n1 start),(decorate_exp n2 start),start)
    | Malloc(id,l) -> if not (List.mem id start) then failwith "Scope check error: variable not declared" ;n
    | Block (n1)-> Block(decorate_tree n1 start)
    | Empty -> n
)
and decorate_exp e start= 
 (match e with
   Variable(id,l) -> if not (List.mem id start) then failwith "Scope check error: variable not declared" ;e
    | Procedure(id,n1,l) -> Procedure (id,(decorate_tree n1 (id::start)),start)
    | Math(op,n1,n2,l) -> Math (op ,(decorate_exp n1 start),(decorate_exp n2 start),start)
    | Integer(value) -> e
    | Minus(n1,l) -> Minus ((decorate_exp n1 start) ,start)
    | Null -> e
    | FieldLocation(n1,n2,l) -> FieldLocation ((decorate_exp n1 start),(decorate_exp n2 start),start)
    | Field (id,l) -> e
 )

and decorate_bool b start =
(match b with
	True -> b
    | False ->  b
    | Equals(n1,n2,l) -> Equals ((decorate_exp n1 start),(decorate_exp n2 start),start)
    | Lessthan(n1,n2,l) -> Lessthan ((decorate_exp n1 start),(decorate_exp n2 start),start)
)


let rec process_tree config=
    (match config with
    Conf(command,stack,heap) ->
        (match command with
            Empty -> Conf(Empty,stack,heap)
            | Block(n1) -> let nextCommand = process_tree (Conf(n1,stack,heap)) in
                           (match nextCommand with
                            Conf(Empty,newstack,newheap) -> 
                            Conf(Empty,(check_and_restore newstack),newheap) 
                            | Conf(comm,newstack,newheap) -> Conf(Block comm,newstack,newheap)
                            )
            |Declaration(id,n1,l) -> let myframe = Decl(Env(Var(id) ,  Object(Int(List.length !heap)))) 
                                    in heap := !heap @ [HeapEntry(ref[Val , ref (Value(VLocation(Nulllocation)))])];
                                    Conf(Block n1,myframe::stack,heap)
            | VarAssign(id,n1,l) ->  let toSet = evalexp n1 stack heap
                                  and heaploc = getHeapLocation id stack
                                  in setHeapValue !heap heaploc toSet;
                                  Conf(Empty,stack,heap)
            | FieldAssign(n1,n2,n3,l) -> let e1 = evalexp n1 stack heap
                                         and e2 = evalexp n2 stack heap
                                         and e3 = evalexp n3 stack heap
                                        in
                                        (match e1,e2 with
                                            Value(VLocation(Location(Object(Int(pos))))), Value(Vfield(vfield))-> 
                                            setHeapField pos (Value(Vfield(vfield))) e3 heap ;
                                            Conf(Empty,stack,heap)
                                         | _,_ ->  failwith "Assigning a field to a variable that hasn't been malloced"
                                    )
            | Skip -> Conf(Empty,stack,heap)
            | Sequence(n1,n2,l) -> let nextCommand = process_tree (Conf(n1,stack,heap))
                                   in

                                   (match nextCommand with
                                    Conf(myblock,newstack,newheap) -> 
                                    (match myblock with 
                                    Empty -> Conf(n2, newstack,heap)
                                    | comm -> Conf(Sequence(comm,n2,l),newstack,newheap)
                                    ))
            | While(n1,n2,l) -> let eb = evalbool n1 stack heap
                                in (match eb with
                                    Btrue -> Conf(Sequence(n2,While(n1,n2,l),l),stack,heap)
                                    | Bfalse -> Conf(Empty,stack,heap)
                                    | Berror -> failwith "Boolean type error"
                                    ) 
            | If(n1,n2,n3,l) -> let eb = evalbool n1 stack heap
                                in (match eb with
                                Btrue -> Conf(n2,stack,heap)
                                | Bfalse -> Conf(n3,stack,heap)
                                | Berror -> failwith "Boolean type error"
                                )
            | Atom(n1,l) -> let nextCommand = process_tree (Conf(Block(n1),stack,heap))
                            in
                            (match nextCommand with
                            Conf(myblock,newstack,newheap) -> 
                                (match myblock with 
                                Empty -> Conf(Empty,stack,heap)
                                | comm -> process_tree (Conf(Atom(command,l),newstack,newheap))
                                ))
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
            | Call(n1,n2,l) -> let e1 = evalexp n1 stack heap and
                               e2 = evalexp n2 stack heap
                                in
                                (match e1 with
                                    Value(Clo(Var(param),body,callstack)) -> let myframe = FCall((Env(Var(param) ,  Object(Int(List.length !heap)))),stack) 
                                                                             in heap := !heap @ [HeapEntry(ref[Val , ref (e2)])];
                                                                             Conf(Block(body),myframe::callstack,heap)
                                    | _ -> failwith "Calling a function that isn't a function"  
                                )
                                 
            | Malloc(id,l) -> let pos = getHeapLocation id stack in
                              genNewInHeap pos heap;
                              Conf(Empty,stack,heap)
            )
        )
and process_control config =
    let next = process_tree config
        in 
    (match next with
    Conf(myblock,stack,heap) -> 
        (match myblock with 
        Empty -> 
            print_string "**************Stack and heap dump**************\n";
            print_newline ();
            print_stack stack !heap;
            print_newline ();
            print_string "Next Command\n";
            print_string "Program Terminates\n";
            flush stdout;
        | comm -> 
            print_string "**************Stack and heap dump**************\n";
            print_newline ();
            print_stack stack !heap;
            print_newline ();
            flush stdout;
            print_string "\n**************Next Command**************\n";
            print_tree comm;
            print_newline ();
            flush stdout;
            process_control next
        )
    )



let run tree =
    print_string "**************Program Starting**************\n";
    print_tree tree;
    print_newline ();
    process_control (Conf((decorate_tree tree []),[], ref([] : heapType)))