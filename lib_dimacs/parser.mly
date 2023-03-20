%token EOF
%token P CNF
%token <int> INT
%token ZERO

%start main
%type <int * int * int list list> main

%%

main:
    | problem EOF { $1 }

problem:
    | P CNF nvars=INT nclauses=INT cls=clause+
        { (nvars, nclauses, cls) }

clause:
    | l=literal+ ZERO { l }

literal:
    | INT { $1 }