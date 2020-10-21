union exception = {
  Error_not_implemented : string,
  Error_internal_error  : unit
}

/*val not_implemented : forall ('a : Type). string -> 'a effect {escape}*/
val not_implemented : string -> int effect {escape}
function not_implemented message = throw(Error_not_implemented(message))

/*
val internal_error : forall ('a : Type). string -> 'a effect {escape}
function internal_error(s) = {
    assert (false, s);
    throw Error_internal_error()
}
*/