datatype expr =
    ATOM of string
    LIST of expr vector

parseAtom (str: string): expr

fun parseExpr (str: string): expr option = 
    if String.size str <= 0 then NONE else
    case String.sub (str, 0) of 
        #"(" => parseList (String.extract (str, 1, NONE))
        c => parseAtom str

fun ppExpr (e: expr): string = 
    case e of
        ATOM s => s
        LIST l => "(" ^ (ppExpr l) ^ ")"

fun main () = 
    let 
        open TextIO
        val inp = inputAll stdIn
        val prog = parseExpr inp
        val repr = ppExpr prog
    in 
        output (stdOut, repr ^ "\n")
    end

val = main ()