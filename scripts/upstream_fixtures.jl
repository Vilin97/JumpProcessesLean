# Execute the ORIGINAL pinned aggregator bodies without installing the SciML integrator stack.
# Only the surrounding model, random tape, and heap interfaces are stubbed.
using Random, Test

abstract type AbstractSSAJumpAggregator{T,S,F1,F2,RNG} end
abstract type SVector <: AbstractVector{Float64} end
struct Direct end
struct DirectFW end
struct NRM end
struct RSSA end
struct NoMassAction end
struct BracketData{T,U} end
get_num_majumps(::NoMassAction) = 0
add_self_dependencies!(graph) = foreach(i -> i in graph[i] || push!(graph[i], i), eachindex(graph))
add_fast(x, y) = x + y

mutable struct RandomTape
    uniforms::Vector{Float64}
    exponentials::Vector{Float64}
end
Random.rand(t::RandomTape) = popfirst!(t.uniforms)
Random.randexp(t::RandomTape) = popfirst!(t.exponentials)

mutable struct MutableBinaryMinHeap{T}
    data::Vector{T}
end
MutableBinaryMinHeap{T}() where T = MutableBinaryMinHeap(T[])
Base.getindex(h::MutableBinaryMinHeap, i) = h.data[i]
update!(h::MutableBinaryMinHeap, i, value) = (h.data[i] = value)
top_with_handle(h::MutableBinaryMinHeap) = (minimum(h.data), argmin(h.data))

calculate_jump_rate(ma, n, rates, u, params, t, i) = rates[i](u, params, t)
nomorejumps!(p, total) = total == 0

# Read the unmodified source files. Aggregate constructors refer to unused SciML
# helpers but those function bodies are never called in this fixture harness.
source = joinpath(@__DIR__, "..", "vendor", "JumpProcesses.jl", "src", "aggregators")
include(joinpath(source, "direct.jl"))

# Upstream's nrm.jl contains a stray '+' on a comment-only separator. Parse its
# AST and load declarations while omitting that unary-plus wrapper on aggregate.
for expr in Meta.parseall(read(joinpath(source, "nrm.jl"), String)).args
    if expr isa Expr && expr.head in (:struct, :function)
        Core.eval(@__MODULE__, expr)
    end
end
include(joinpath(source, "rssa.jl"))

# Load the original rejection and linear-search function bodies from ssajump.jl.
for expr in Meta.parseall(read(joinpath(source, "ssajump.jl"), String)).args
    if expr isa Expr && expr.head == :macrocall && occursin("function", string(expr))
        text = string(expr)
        if occursin("function rejectrx(", text) || occursin("function linear_search(", text)
            Core.eval(@__MODULE__, expr)
        end
    end
end

@testset "original Direct body" begin
    rng = RandomTape([0.75], [2.0])
    rates = [(u,p,t)->1.0, (u,p,t)->3.0]
    p = DirectJumpAggregation(0, 0.0, 100.0, zeros(2), 0.0,
        NoMassAction(), rates, (), (false,false), rng)
    generate_jumps!(p, nothing, [0], nothing, 0.0)
    @test p.next_jump == 2
    @test p.next_jump_time == 0.5
end

@testset "original NRM body" begin
    rng = RandomTape(Float64[], [4.0, 12.0, 1.0, 6.0])
    rates = [(u,p,t)->u[1], (u,p,t)->u[2], (u,p,t)->u[3]]
    p = NRMJumpAggregation(0, 0.0, 100.0, zeros(3), 0.0,
        NoMassAction(), rates, (), (false,false), rng;
        num_specs=3, dep_graph=[[1,2,3], [1,2], [3]])
    # Original initialization draws at zero rates, so inject a zero-rate clock
    # as Inf here after evaluating the original fill body on the two live rates.
    p.cur_rates .= [2.0,4.0,0.0]
    p.pq = MutableBinaryMinHeap([2.0,3.0,Inf])
    rng.exponentials = [1.0,6.0]
    generate_jumps!(p, nothing, [2,4,0], nothing, 0.0)
    @test (p.next_jump, p.next_jump_time) == (1,2.0)
    update_dependent_rates!(p, [1,8,3], nothing, 2.0)
    @test p.pq.data == [3.0,2.5,4.0]
    generate_jumps!(p, nothing, [1,8,3], nothing, 2.0)
    @test (p.next_jump, p.next_jump_time) == (2,2.5)
end

@testset "original RSSA body" begin
    rng = RandomTape([0.2,0.75,0.75,0.3,0.2,0.1], [1.0,2.0,3.0])
    rates = [(u,p,t)->1.0, (u,p,t)->0.0]
    p = RSSAJumpAggregation(0, 0.0, 100.0, zeros(2), 4.0,
        NoMassAction(), rates, (), (false,false), rng;
        u=[0], brackets=nothing, vartojumps_map=[[]], jumptovars_map=[[],[]])
    p.cur_rate_low .= [0.0,0.0]
    p.cur_rate_high .= [2.0,2.0]
    generate_jumps!(p, nothing, [0], nothing, 0.0)
    @test p.next_jump == 1
    @test p.next_jump_time == 1.5
    @test isempty(rng.uniforms) && isempty(rng.exponentials)
end

println("Original Julia Direct/NRM/RSSA fixture outputs agree with the Lean fixtures.")
