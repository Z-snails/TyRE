module Benchmark

import System.Clock

public export
record Benchmark where
    constructor MkBench
    {0 input : Type}
    {0 output : Type}
    name : String
    -- Generate input of a given size using input of a previous size
    genInput : Nat -> Maybe input -> input
    run : input -> IO output

%foreign "scheme:collect"
prim__collect : PrimIO ()

collect : IO ()
collect = primIO $ prim__collect

%foreign "scheme:collect-request-handler void"
prim__disable_gc : PrimIO ()

disable_gc : IO ()
disable_gc = primIO $ prim__disable_gc

record Stats where
    constructor MkStats
    mean : Double
    stddev : Double

nanoScale : Double
nanoScale = 1 / 1_000_000_000

parameters
    (bench : Benchmark)
    (max : Nat)
    (samples : Nat)

    getTimes : Nat -> bench.input -> List (Clock Duration) -> IO (List (Clock Duration))
    getTimes Z inp acc = pure acc
    getTimes (S k) inp acc = do
        collect
        start <- clockTime Monotonic
        _ <- bench.run inp
        end <- clockTime Monotonic
        getTimes k inp (timeDifference end start :: acc)

    getStats : List (Clock Duration) -> Stats
    getStats xs =
        let xs = map (\c => nanoScale * cast (toNano c)) xs
            n = cast $ length xs
            xSum = sum xs
            mean = xSum / n

            sqDiff = sum $ map (\x => let diff = x - mean in diff * diff) xs

            var =  sqDiff / (n - 1)

            stddev = sqrt var
        in MkStats mean stddev

    export
    time : IO ()
    time = disable_gc >> go [0..max] Nothing
      where
        go : List Nat -> Maybe bench.input -> IO ()
        go [] _ = pure ()
        go (size :: ss) inp = do
            let inp' = bench.genInput size inp
            _ <- getTimes 5 inp' [] -- Warmup - these seems to avoid the big spikes
            ts <- getTimes samples inp' []
            let stats = getStats ts
            putStrLn "\{bench.name},\{show size},\{show stats.mean},\{show stats.stddev}"
            go ss (Just inp')

export
printHeader : IO ()
printHeader = putStrLn "Name,Size,Mean,StdDev"
