(* 
Alex Halter
HPL Spring 14

  File miniLEX.mll *)
{
open MiniYACC;;

exception Eof;;
}
let digit = ['0'-'9'] 
let digits = digit + 
let lower_case = ['a'-'z'] 
let upper_case = ['A'-'Z'] 
let letter = upper_case | lower_case 

rule token = parse
    [' ' '\t'] { token lexbuf } (* skip blanks and tabs *)
  | ['\n' ]    { EOL }
  | ';'        { SEMI }
  | ':'        { COLON }
  | '{'         {LBRACK}
  | '}'        {RBRACK}
  | '=''='    { EQUALS }
  | '='       { ASSIGN }
  | '+'        { PLUS }
  | '-'        { MINUS }
  | '.'        { DOT }
  | '*'        { MULT }
  | '/'        { DIV }
  | '('        { LPAR }
  | ')'        { RPAR }
  | '<'        { LT }
  | "var"        {  VAR  }
  | "while"       { WHILE }
  | "then"       { THEN }
  | "proc"        { PROC }
  | "true"        { TRUE }
  | "false"        { FALSE }
  | "malloc"        { MALLOC }
  | "if"        { IF }
  | "else"        { ELSE }
  | '|''|''|'        { CONCURR }
  | "atom"        { ATOM }
  | "null"        { NULL }
  | "skip"        { SKIP }
  | (lower_case)(letter | digit)* as idt
               { IDENT idt}
  | (upper_case)(letter | digit)* as fieldidt
               { FIELD fieldidt}
  | digits as num
               { INTEGER (int_of_string num) }
  | eof        { raise Eof }


