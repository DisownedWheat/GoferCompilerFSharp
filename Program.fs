let print a = System.Console.WriteLine($"{a}")

[<EntryPoint>]
let main _ =
    ignore
    <| match Lexer.lexInputFile "./test_file" with
       | Error e -> printfn "%A" e
       | Ok tokens ->
           // printfn "\n\n\n%A\n\n\n" tokens
           Parser.parse tokens |> print

    0
