
%{ 
(* 
Alex Halter
HPL Spring 14
File miniYACC.mly *)


  
 open AstTree


%} /* declarations */

%token EOL SEMI ASSIGN PLUS /* lexer tokens */
%token MINUS MULT DIV LPAR RPAR 
%token EQUALS LT DOT WHILE THEN
%token PROC TRUE FALSE MALLOC IF ELSE 
%token CONCURR ATOM NULL SKIP COLON LBRACK RBRACK
%token  VAR
%token  INTEGER
%start prog                   /* the entry point */
%type <unit> prog 
%type <AstTree.cmdNode>     cmd assign seqcon parallel 
%type <AstTree.expNode> expr location fieldLocation
%type <AstTree.boolNode> boolean
%token < string > IDENT
%token < string > FIELD
%token < int > INTEGER
%left ASSIGN
%left PLUS MINUS       /* lowest precedence */
%left TIMES DIV             /* medium precedence */
%left DOT LT EQUALS
%nonassoc UMINUS           /* highest precedence */


%% /* rules */
prog :
    cmd EOL  {
      AstTree.run $1
    }
  

cmd :
   assign                  {$1}
  | seqcon                {$1}
  | expr LPAR expr RPAR     { Call($1,$3,[])}
  | VAR IDENT SEMI cmd       {Declaration($2,$4,[])}
  | MALLOC LPAR IDENT RPAR  {Malloc($3,[])}
  | parallel                {$1}


expr :
    expr PLUS expr           { Math(AstTree.Plus,$1,$3,[])  }
  | expr MINUS expr          { Math(AstTree.Sub,$1,$3,[]) }
  | expr TIMES expr          { Math(AstTree.Mult,$1,$3,[])  }
  | expr DIV expr            { Math(AstTree.Div,$1,$3,[]) }
  | MINUS expr %prec UMINUS  { Minus($2,[])}
  | PROC IDENT COLON cmd               {Procedure($2,$4,[])}
  | location                {$1 }
  | INTEGER                     {Integer($1)}
  | FIELD                     {Field($1,[])}

parallel:
  LBRACK cmd CONCURR cmd RBRACK {Concurrent($2,$4,[])}
  | ATOM LPAR cmd RPAR          { Atom ($3,[])}

boolean :
  TRUE                      {True}
  | FALSE                     {False}
  | expr EQUALS expr           {Equals($1,$3,[])}
  | expr LT expr            {Lessthan($1,$3,[])}

location: 
  NULL                    { Null }
  | IDENT                  {Variable($1,[])}
  | expr fieldLocation           {FieldLocation($1,$2,[])}

  fieldLocation :
    DOT expr               { $2 }

seqcon:
  SKIP                { Skip }
  | LBRACK cmd SEMI cmd RBRACK { Sequence($2,$4,[])}
  | WHILE boolean cmd           { While($2,$3,[]) }
  | IF boolean cmd ELSE cmd     {If($2,$3,$5,[])}



assign :
    IDENT ASSIGN expr  {VarAssign($1,$3,[]) }
    | expr DOT expr ASSIGN expr {FieldAssign ($1,$3,$5,[])}


%% (* trailer *)