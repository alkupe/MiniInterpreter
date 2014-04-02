
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

type control = Block of cmdNode
            | Empty



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

type heap = heapEntry list

type conf = Conf of control * stack

let realheap = ref([] : heap)
let rec getHeapLocation id stack =
    match stack with
    hd::tl -> ( match hd with 
                Decl(Env(Var(varid),Object(Int(pos)))) -> if id = varid then pos else getHeapLocation id tl
                | _ -> failwith("not yet implemented")

                )
    | [] -> failwith ("heap location error")

let getValue heapVal loc =
    let rec checkAll hv = 
    match hv with 
        hd::tl -> 
                ( match hd with 
                  
                    Val,tv_ref -> (match !tv_ref with Value(v) -> Value(v)
                                    | TError -> failwith "fail"
                                    )
                    | FieldName(name),_ -> Value(VLocation(Location(Object(Int(loc)))))
                                    
                )
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
                                        | TError -> failwith "fail"
                                        ) 
                                    | TError -> failwith "fail"
                                  )
                    | _,_ -> setVal tl
                                    
                )
        | [] -> failwith "Error setting value"
    in 
    match heapVal with
    HeapEntry e -> setVal !e



let rec setHeapValue myheap loc toSet =

    match myheap with 
    hd::tl -> if loc = 0 then setValue hd toSet else setHeapValue tl (loc-1) toSet
    |[] -> failwith "Error setting value"



let setField heapVal field value=
    let rec setFieldHelper hv fieldname hvref= 
        match hv with 
            hd::tl -> 
                    ( match hd with 
                      
                        Val,tv_ref -> failwith "fail"
                        | FieldName(name),tv_ref -> if name = fieldname then   (tv_ref := value ;print_string "HHHHHHH\n") else setFieldHelper tl fieldname hvref
                                        
                    )
            | [] ->  print_string "oookkk";print_int (List.length !hvref);print_string "\n";flush stdout;hvref := (FieldName(fieldname),ref value)::!hvref;realheap := HeapEntry(hvref)::!realheap ;print_string "oookkk2";print_int (List.length !hvref);print_string "\n";()
        in 
        (match heapVal with
        HeapEntry e -> (match field with 
                        Value(Vfield(FieldName(name))) -> setFieldHelper !e name e
                        | _ -> failwith "fail"
                        )
        )

let rec  setHeapField pos field value myheap= 
   match myheap with
    hd::tl -> if pos = 0 then setField hd field value else setHeapField (pos-1) field value tl
    | [] -> failwith "Error setting field"




let rec getHeapValue loc myheap=
    let copy = loc in
    match myheap with 
    hd::tl -> if loc = 0 then getValue hd copy else getHeapValue (loc-1) tl
    |[] -> TError

let rec check_if_malloced_helper heaploc =
    let rec checkAll hl = 
    match hl with 
        hd::tl -> 
                ( match hd with 
                  
                    Val,tv_ref -> print_string "yyy\n";false
                    | FieldName(name),_ -> print_string "nnn\n";true
                                    
                )
        | [] -> print_string "zzzz\n";true
    in 
    match heaploc with
    HeapEntry e -> print_string "aaaaaa\n";checkAll !e
    | _ -> print_string "bbbbb\n"; false

let rec check_if_malloced loc myheap=
        print_string "ccccccc\n";
    match myheap with 
    hd::tl -> if loc = 0 then check_if_malloced_helper hd else check_if_malloced (loc-1) tl
    |[] -> failwith "fail"


 let rec evalexp exp stack =
    match exp with
    Variable(id,l) ->  let heaploc = getHeapLocation id stack in
                        getHeapValue heaploc !realheap
    | Procedure(id,n1,l) -> Value(VLocation(Nulllocation))
    | Integer(value) -> Value(Vint(Int(value)))
    | Math(op,n1,n2,l) -> doMath op n1 n2 stack
    | Minus(n1,l) -> let v1 = evalexp n1 stack in
                        (match v1 with Value(Vint(Int(value1))) -> Value(Vint(Int(-value1)))

                         | _ -> TError)
    | Null -> Value(VLocation(Nulllocation))
    | FieldLocation(n1,n2,l) -> Value(VLocation(Nulllocation)) (*let v1 = evalexp n1 stack
                                and v2 = evalexp n2 stack
                                in
                                (match v1 with
                                Value(Location(Object(Int(pos)))) -> 
                                | _ -> failwith "fail"
                                )*)
    | Field(id,l) -> Value(Vfield(FieldName(id)))
and
    doMath op n1 n2 stack =
    match op with
    Sub -> let v1 = evalexp n1 stack
            and v2 = evalexp n2 stack
            in (match v1,v2 with
                Value(Vint(Int(value1))),Value(Vint(Int(value2))) ->  Value(Vint(Int(value1 - value2)))
                |_,_ -> TError )
    |Plus -> failwith "math op not implemented"
    |Mult -> failwith "math op not implemented"
    |Div -> failwith "math op not implemented"


 let rec evalbool bool stack = 
    match bool with 
    True -> Btrue
    | False -> Bfalse
    | Equals (e1,e2,l) -> let v1 = evalexp e1 stack
                          and v2 = evalexp e2 stack
                          in (match v1,v2 with
                             Value(Vint(Int(value1))),Value(Vint(Int(value2))) -> if value1 = value2 then Btrue else Bfalse
                             | _,_ -> Berror
                          )
     | Lessthan (e1,e2,l) -> let v1 = evalexp e1 stack
                            and v2 = evalexp e2 stack
                            in (match v1,v2 with
                             Value(Vint(Int(value1))),Value(Vint(Int(value2))) -> if value1 < value2 then Btrue else Bfalse
                             | _,_ -> Berror
                          )


let rec print_heap_fields heapValue =
    let rec printField hv = 
    match hv with 
        hd::tl -> 
                ( match hd with 
                  
                    Val,tv_ref -> (match !tv_ref with Value(Vint(Int(myval))) -> 
                                    print_string "value = "; print_int myval; print_string "\n"; flush stdout
                                    | _ -> ()
                                  )
                    | FieldName(name),tv_ref -> (match !tv_ref with Value(Vint(Int(myval))) -> 
                                                print_string ("field name " ^ name ^ " = "); print_int myval; print_string "\n"; flush stdout;
                                                printField tl
                                                | _ -> ()
                                              )
                                    
                )
        | [] -> ()
    in 
    match heapValue with
    HeapEntry e -> printField !e

let rec print_heap loc myheap=
    match myheap with 
    hd::tl -> if loc = 0 then print_heap_fields hd else print_heap (loc-1) tl 
    |[] -> failwith "Error printing value"



let rec print_stack stack =
    match stack with
    hd::tl -> ( match hd with 
                Decl(Env(Var(id) ,  Object(Int(loc)))) -> print_string ("Printing heap for " ^ id ^ "\n");
                 print_heap loc !realheap;print_stack tl
                | _-> ()
                )
    | [] -> ()



let print_op op =
    match op with
    Plus -> "plus"
    | Sub -> "minus"
    | Mult -> "mult"
    | Div -> "div"


let change_heap_location stack frame =
    let rec removestack stack id =
    match stack with
    hd::tl -> (match hd with
            Decl(Env(Var(checkid) ,  Object(Int(pos)))) -> if id = checkid then stack @ tl else removestack (hd::stack) id
            | _ -> removestack (hd::stack) id
            )
    | [] -> stack
    in 
    (match frame with
    Decl(Env(Var(id) ,  Object(Int(newpos)))) ->  frame::(removestack stack id)
    | _ -> failwith "fail")



 let rec print_tree n = 
  (match n with
      Declaration(id,n1,l) -> print_string ("Declaration(" ^ id ^ " in ");print_tree n1;print_string ")\n"; flush stdout;()
    | VarAssign(id,n1,l) -> print_string ("Variable Assignment (\n" ^ id) ;print_newline();print_exp n1;print_string ")\n"; flush stdout;()
    | FieldAssign(n1,n2,n3,l) -> print_string "Field Assignment(\n"; print_exp n1; print_exp n2; print_exp n3; print_string ")\n"; flush stdout;()
    | Skip ->()
    | Sequence(n1,n2,l) -> print_string "Sequence(\n";print_tree n1;print_tree n2 ;print_string ")\n"; flush stdout;()
    | While(n1,n2,l) -> print_string "While(\n";print_bool n1 ;print_tree n2 ;print_string")\n"; flush stdout;()
    | If(n1,n2,n3,l) -> print_string "If(\n";print_bool n1 ; print_string ")Then(\n"; print_tree n2 ;print_string ")Else(\n"; print_tree n3 ;print_string")\n"; flush stdout;()
    | Atom(n1,l) -> print_string "Atom(\n";print_tree n1 ;print_string")\n"; flush stdout;()
    | Concurrent(n1,n2,l) -> print_string "Concurrent(\n";print_tree n1 ;print_tree n2 ;print_string")\n"; flush stdout;()
    | Call(n1,n2,l) -> print_string "Call(\n";print_exp n1 ;print_exp n2 ;print_string")\n"; flush stdout;()
    | Malloc(id,l) -> print_string "Malloc(\n";print_string id;print_string")\n"; flush stdout;() 
    )
and print_exp e = 
 (match e with
   Variable(id,l) -> print_string id;print_newline();flush stdout;()
    | Procedure(id,n1,l) -> print_string id; print_tree n1;flush stdout;()
    | Integer(value) -> print_int value;flush stdout;()
    | Math(op,n1,n2,l) -> print_string ((print_op op) ^ "(\n");print_exp n1;print_exp n2 ;print_string ")\n"; flush stdout;()
    | Minus(n1,l) -> print_string "Minus(\n" ; print_exp n1;print_string")\n"; flush stdout;()
    | Null -> ()
    | FieldLocation(n1,n2,l) -> print_exp n1; print_exp n2 ;()
    | Field(id,l) -> print_string id;print_newline();flush stdout;()
 )

and print_bool b =
(match b with
	True -> print_string "true\n";flush stdout;()
    | False -> print_string "false\n";flush stdout;()
    | Equals(n1,n2,l) -> print_string "Equals(\n";print_exp n1; print_exp n2 ;print_string")\n"; flush stdout;()
    | Lessthan(n1,n2,l) -> print_string "Less Than(\n" ; print_exp n1 ; print_exp n2 ;print_string")\n"; flush stdout;()
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
    | VarAssign(id,n1,l) -> if not (List.mem id start) then  failwith "variable not declared1"; VarAssign(id,decorate_exp n1 start,start)
    | FieldAssign(n1,n2,n3,l) -> FieldAssign((decorate_exp n1 start),(decorate_exp n2 start),(decorate_exp n3 start),start) 
    | Skip -> n
    | Sequence(n1,n2,l) -> Sequence ((decorate_tree n1 start) ,(decorate_tree n2 start) ,start)
    | While(n1,n2,l) -> While((decorate_bool n1 start),(decorate_tree n2 start),start)
    | If(n1,n2,n3,l) -> If ((decorate_bool n1 start),(decorate_tree n2 start),(decorate_tree n3 start),start)
    | Atom(n1,l) -> Atom((decorate_tree n1 start),start)
    | Concurrent(n1,n2,l) ->  Concurrent ((decorate_tree n1 start),(decorate_tree n2 start),start)
    | Call(n1,n2,l) -> Call ((decorate_exp n1 start),(decorate_exp n2 start),start)
    | Malloc(id,l) -> if not (List.mem id start) then failwith "variable not declared2" ;n
)
and decorate_exp e start= 
 (match e with
   Variable(id,l) -> if not (List.mem id start) then failwith "variable not declared3" ;e
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
    Conf(myblock,stack) ->
        (match myblock with
        Empty -> Conf(Empty,stack)
        | Block(command) ->
            (match command with 
            Declaration(id,n1,l) -> let myframe = Decl(Env(Var(id) ,  Object(Int(List.length !realheap)))) 
                                    in realheap := HeapEntry(ref[Val , ref (Value(VLocation(Nulllocation)))]) :: !realheap;
                                    Conf(Block n1,myframe::stack)
            | VarAssign(id,n1,l) ->  let toSet = evalexp n1 stack
                                  and heaploc = getHeapLocation id stack
                                  in setHeapValue !realheap heaploc toSet;
                                  Conf(Empty,stack)
            | FieldAssign(n1,n2,n3,l) -> let e1 = evalexp n1 stack
                                         and e2 = evalexp n2 stack
                                         and e3 = evalexp n3 stack
                                        in
                                        (match e1,e2 with
                                            Value(VLocation(Location(Object(Int(pos))))), Value(Vfield(vfield))-> 
                                            print_string "hhhhh\n\n";
                                            setHeapField pos (Value(Vfield(vfield))) e3 !realheap ;
                                            Conf(Empty,stack)
                                         | _,_ ->  failwith "Assigning a field to a variable that hasn't been malloced"
                                    )
            | Skip -> Conf(Empty,stack)
            | Sequence(n1,n2,l) -> let nextCommand = process_tree (Conf(Block(n1),stack))
                                   in
                                   (match nextCommand with
                                    Conf(myblock,newstack) -> 
                                    (match myblock with 
                                    Empty -> Conf(Block(n2),stack)
                                    | Block(command) -> process_tree (Conf(Block(Sequence(command,n2,l)),newstack))
                                    ))
            | While(n1,n2,l) -> let eb = evalbool n1 stack
                                in (match eb with
                                    Btrue -> Conf(Block(Sequence(n2,While(n1,n2,l),l)),stack)
                                    | Bfalse -> Conf(Empty,stack)
                                    | Berror -> failwith "boolean expression error"
                                    ) 
            | If(n1,n2,n3,l) -> let eb = evalbool n1 stack
                                in (match eb with
                                Btrue -> Conf(Block(n2),stack)
                                | Bfalse -> Conf(Block(n3),stack)
                                | Berror -> failwith "boolean expression error" 
                                )
            | Atom(n1,l) -> let nextCommand = process_tree (Conf(Block(n1),stack))
                            in
                            (match nextCommand with
                            Conf(myblock,newstack) -> 
                                (match myblock with 
                                Empty -> Conf(Empty,stack)
                                | Block(command) -> process_tree (Conf(Block(Atom(command,l)),newstack))
                                ))
            | Concurrent(n1,n2,l) -> Conf(Empty,stack)
            | Call(n1,n2,l) -> Conf(Empty,stack)
            | Malloc(id,l) -> let myframe = Decl(Env(Var(id) ,  Object(Int(List.length !realheap))))
                              in 
                              realheap := HeapEntry(ref[]) :: !realheap;
                              Conf(Empty,(change_heap_location stack myframe))
            )
        )
    )
and process_control config =
    let next = process_tree config
    in 
    (match next with
    Conf(myblock,stack) -> 
        (match myblock with 
        Empty -> 
            print_string "**************Stack and heap dump**************\n";
            print_newline ();
            print_stack stack;
            print_newline ();
            print_string "Next Command\n";
            print_string "Program Terminates\n";
            flush stdout;
        | Block(command) -> 
            print_string "**************Stack and heap dump here**************\n";
            print_newline ();
            print_stack stack;
            print_newline ();
            print_string "Next Command\n";
            flush stdout;
            let next = process_tree (Conf(Block(command),stack))
            in
            print_string "Block(\n";
            flush stdout;
            print_tree command;
            print_string ")\n";
            flush stdout;
            process_control next
        )
    )



let run tree =
    process_control (Conf(Block(decorate_tree tree []), []))