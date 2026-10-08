# Benchmark JumpProcesses.jl aggregators on `.rn` networks.
#
# usage: julia --project=bench/julia bench/julia/bench.jl <model.rn> <T> <reps> <out.json> <method>...
#
# Each method is timed on full `solve` calls over (0, T) with `SSAStepper`, no saving, and
# a fresh Xoshiro seed per repetition, after one warm-up solve. The number of events of
# every timed repetition is counted by a separate stepping run with the same seed.
using JumpProcesses, JSON, Random, Statistics

function read_rn(path)
    lines = readlines(path)
    lines[1] == "jprn 1" || error("not a jprn file")
    numspecies = parse(Int, split(lines[2])[2])
    u0 = parse.(Int, split(lines[3]))
    length(u0) == numspecies || error("bad population line")
    numrx = parse(Int, split(lines[4])[2])
    rates = Vector{Float64}(undef, numrx)
    rstoch = Vector{Vector{Pair{Int, Int}}}(undef, numrx)
    nstoch = Vector{Vector{Pair{Int, Int}}}(undef, numrx)
    for j in 1:numrx
        f = split(lines[4 + j])
        rates[j] = reinterpret(Float64, parse(UInt64, f[1]; base = 16))
        r = parse(Int, f[2])
        r > 0 || error("zero-order reactions are not supported")
        k = 3
        rs = Pair{Int, Int}[]
        for _ in 1:r
            push!(rs, (parse(Int, f[k]) + 1) => parse(Int, f[k + 1]))
            k += 2
        end
        c = parse(Int, f[k])
        k += 1
        ns = Pair{Int, Int}[]
        for _ in 1:c
            push!(ns, (parse(Int, f[k]) + 1) => parse(Int, f[k + 1]))
            k += 2
        end
        rstoch[j] = rs
        nstoch[j] = ns
    end
    u0, rates, rstoch, nstoch
end

const AGGREGATORS = Dict("Direct" => Direct, "SortingDirect" => SortingDirect,
    "RDirect" => RDirect, "FRM" => FRM, "NRM" => NRM, "CCNRM" => CCNRM,
    "DirectCR" => DirectCR, "RSSA" => RSSA, "RSSACR" => RSSACR)

function problem(network, T, aggregator, seed)
    u0, rates, rstoch, nstoch = network
    jumps = MassActionJump(rates, rstoch, nstoch; scale_rates = false)
    dprob = DiscreteProblem(copy(u0), (0.0, T), nothing)
    JumpProblem(dprob, aggregator(), jumps; save_positions = (false, false),
        rng = Xoshiro(seed))
end

function count_events(jprob, T)
    integrator = init(jprob, SSAStepper())
    events = 0
    while integrator.t < T
        step!(integrator)
        integrator.t < T && (events += 1)
    end
    events
end

function main(args)
    path, T, reps, out = args[1], parse(Float64, args[2]), parse(Int, args[3]), args[4]
    methods = args[5:end]
    network = read_rn(path)
    results = Dict{String, Any}()
    for name in methods
        aggregator = AGGREGATORS[name]
        warm = problem(network, T / 100, aggregator, 1)
        solve(warm, SSAStepper())
        times = Float64[]
        events = Int[]
        for rep in 1:reps
            seed = 1000 + rep
            jprob = problem(network, T, aggregator, seed)
            GC.gc()
            push!(times, @elapsed solve(jprob, SSAStepper()))
            push!(events, count_events(problem(network, T, aggregator, seed), T))
        end
        results[name] = Dict("times" => times, "events" => events,
            "median_time" => median(times), "mean_events" => mean(events),
            "events_per_second" => sum(events) / sum(times))
        println(rpad(name, 14), " median ", round(median(times); sigdigits = 4), " s, ",
            round(mean(events); sigdigits = 5), " events, ",
            round(sum(events) / sum(times); sigdigits = 4), " events/s")
        flush(stdout)
    end
    meta = Dict("model" => basename(path), "T" => T, "reps" => reps,
        "julia" => string(VERSION),
        "JumpProcesses" => string(pkgversion(JumpProcesses)), "threads" => Threads.nthreads())
    open(out, "w") do io
        JSON.print(io, Dict("meta" => meta, "results" => results), 2)
    end
end

main(ARGS)
