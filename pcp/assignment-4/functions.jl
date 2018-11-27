# Σ(\Sigma)

# nice and readable
function Σ1(f, n::Int, m::Int)::Int
    sum = 0
    for i = n:m
        sum += f(i)
    end
    return sum
end

n = 1
m = 3
f = a -> a^2
result = Σ1(f, n, m)

print("Normal (Σ1): ")
println(result)


# weird and compact
Σ2(f, n, m) = n ≤ m ? f(n) + Σ2(f, n + 1, m) : 0

arguments = (f, n, m)
result = Σ2(arguments...)

print("Recursive (Σ2): ")
println(result)


