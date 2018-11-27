# tasks (symmetric coroutines)
println("-- Tasks")

producer = @task begin
    for i = 1:3
        yieldto(consumer, i * 2)
    end
end

consumer = @task begin
    while true
        println(yieldto(producer))
    end
end

schedule(producer)
schedule(consumer)
wait(producer)
