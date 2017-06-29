val fatorial = (LETREC ( "fat", TINT, TINT, "x", TINT, (IF ( (BOP ( (VAR "x"), EQ, (ENUM 0))), (ENUM 1), (BOP ( (VAR "x"), MULT, (APP ( (VAR "fat"), (BOP ( (VAR "x"), DIFF, (ENUM 1))))))))), (APP ((VAR "fat"), (ENUM 5)))))

val fn = (FN ("x", TINT, (VAR "x")))

                    
val app = (APP ((FN ("x", TINT, (VAR "x"))), (ENUM 0)))
