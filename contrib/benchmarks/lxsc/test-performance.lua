#!/usr/bin/env lua

package.path = 'LXSC/?.lua;' .. package.path

require 'io'
require 'os'
local LXSC = require 'lxsc'

local c,t,lxsc = os.clock

local out = io.open(string.format("results-%s.txt",LXSC.VERSION),"w")
local sum=0
function mark(msg,t2,n)
  local delta = (t2-t)*1000/(n or 1)
  sum = sum + delta
  out:write(string.format("%25s: %5.2fms\n",msg,delta))  
end

local xml = io.open("test.scxml"):read("*all")
t = c()
for i=1,20 do lxsc = LXSC:parse(xml) end
mark("Parse XML",c(),20)

lxsc.onAfterEnter = function(id,kind) 
	if (id=="id401") then
		print("Entered "..kind.." '"..tostring(id).."'") 
	end
end

t = c()
lxsc:start()
mark("Start Machine",c())


out:write("----------------------------------\n")
out:write(string.format("%25s: %5.2fms ± 20%%\n","Total time",sum))  

out:close()