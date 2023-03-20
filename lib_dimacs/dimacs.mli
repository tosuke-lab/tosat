type parse_err = Lexing.position * string
type parse_result = (int list list, parse_err) Result.t

val parse : Lexing.lexbuf -> parse_result
