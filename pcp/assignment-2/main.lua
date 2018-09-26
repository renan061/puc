local math = require("math")

local space = "        \t"

local function speedup(n, p)
    local ts = math.pow(n, 2)
    local log2p = math.log(p) / math.log(2)
    local tp = math.pow(n, 2) / p + log2p
    return ts / tp
end

local function efficiency(s, p)
    return s / p
end

io.write("\n\n")

-- header processors
io.write("(s, e)")
io.write(space)
for i = 1, 8 do
    io.write("p = " .. math.floor(math.pow(2, i - 1)) .. space)
end
io.write("\n")
for i = 1, 144 do
    io.write("-")
end
io.write("\n")

-- table
for i = 1, 6 do
    local n = math.floor(math.pow(2, i - 1) * 10)
    io.write("n = " .. n .. space) -- header input size
    for j = 1, 8 do
        local p = math.floor(math.pow(2, j - 1))
        local s = speedup(n, p)
        local e = string.format("%.3f", efficiency(s, p))
        io.write(string.format("%.3f", s) .. ", " .. e .. "\t")
    end
    io.write("\n")
end

io.write("\n\n")
