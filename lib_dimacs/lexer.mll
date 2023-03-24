{
    open Parser
}

let space = [' ' '\t' '\n' '\r']
let not_lf = [^'\n']

let zero = '0'
let non_zero = ['1'-'9']
let digit = ['0'-'9']

let intnum = '-'? non_zero digit*

rule token = parse
    | eof       { EOF }
    | "%"       { EOF }
    | space     { token lexbuf } (* skip spaces *)
    | "c"       { comment lexbuf } (* skip comments *)
    | "p"       { P }
    | "cnf"     { CNF }
    | zero      { ZERO }
    | intnum    { INT (int_of_string @@ Lexing.lexeme lexbuf) }
and comment = parse
    | eof       { EOF }
    | '\n'      { token lexbuf }
    | not_lf*   { comment lexbuf }
