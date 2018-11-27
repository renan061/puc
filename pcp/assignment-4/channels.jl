# channels
println("-- Channels")

function producer(c)
    for i = 1:5
        put!(c, i * 2)
    end
    close(c)
end

c = Channel{Int}(1)
@async producer(c)

for i in c
   println(i)
end 
