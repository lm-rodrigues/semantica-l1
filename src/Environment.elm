module Environment exposing (..)


type alias Environment a b =
    List ( a, b )


emptyEnv : Environment a b
emptyEnv =
    []


insertEnv : a -> b -> Environment a b -> Environment a b
insertEnv key value environment =
    ( key, value ) :: environment


envLookup : a -> Environment a b -> Maybe b
envLookup searchKey environment =
    case environment of
        ( key, value ) :: xs ->
            if searchKey == key then
                Just value
            else
                envLookup searchKey xs

        [] ->
            Nothing
