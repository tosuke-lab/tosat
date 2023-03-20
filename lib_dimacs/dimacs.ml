type parse_err = Lexing.position * string
type parse_result = (int list list, parse_err) Result.t

let parse lexbuf =
  try
    let _, _, clauses = Parser.main Lexer.token lexbuf in
    Result.ok clauses
  with e ->
    let start_p = Lexing.lexeme_start_p lexbuf in
    let mes = Printexc.to_string e in
    Result.error (start_p, mes)
