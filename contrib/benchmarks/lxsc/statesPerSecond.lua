#!/usr/bin/env lua

package.path = 'LXSC/?.lua;' .. package.path

require 'io'
require 'os'
local LXSC = require 'lxsc'
local file = ...
local init, mark, now
local iterations = 0

local started = os.clock()
local xml = io.open(file):read("*all")
lxsc = LXSC:parse(xml)

lxsc.onAfterEnter = function(id,kind) 
	if (id=="mark") then
		iterations = iterations + 1
		now = os.clock()
		if (now - mark > 1) then
			print(init .. ", " .. iterations)
			mark = now
			iterations = 0
		end
	end
end

now = os.clock()
init = (now - started) * 1000;
mark = now

lxsc:start()
