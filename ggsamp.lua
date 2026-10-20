script_name('GGSamp')
script_version('1.0')
script_author('brruham')
script_description('Memory scanner ala GG (/gg)')

local ffi   = require('ffi')
local imgui = require('mimgui')

local function readAll(p)
    local f = io.open(p, 'rb')
    if not f then return nil end
    local s = f:read('*a')
    f:close()
    return s
end

local function getPackageName()
    local parts = {}
    for part in string.gmatch(getWorkingDirectory(), '([^/\\]+)') do parts[#parts + 1] = part end
    return parts[#parts - 1]
end

local wd    = getWorkingDirectory()
local soSrc = wd .. '/libggsamp.so'
local soDst = '/data/data/' .. getPackageName() .. '/libggsamp.so'
do
    local a, b = readAll(soSrc), readAll(soDst)
    if a and a ~= b then
        local f = io.open(soDst, 'wb')
        if f then f:write(a) f:close() end
    end
end

ffi.cdef[[
    int gg_init(const char*);
    int gg_run_async(const char*);
    int gg_busy();
    const char* gg_result();
]]

local ok, lib = pcall(ffi.load, soDst)
if ok then lib.gg_init(wd .. '/gg') end

local show   = imgui.new.bool(false)
local bufVal = imgui.new.char[64]()
local bufW   = imgui.new.char[64]()
local TYPES  = { 'i32', 'i8', 'i16', 'i64', 'f32', 'f64' }
local REGS   = { 'ca+a', 'anon', 'all', 'native', 'ch', 'cb', 'cd', 'cs', 'j', 'o' }
local ti, ri = 1, 1
local stype  = 'i32'
local rows, status, busy, job = {}, 'siap', false, nil

local LIST = "local t={} for i,h in ipairs(gg.results(50,0)) do t[#t+1]=string.format('%x|%s',h.addr,tostring(h.value)) end return table.concat(t,'\\n')"

local function clean(buf)  return (ffi.string(buf):gsub('[^%d%.~%-]', '')) end
local function num(buf)
    local s = (ffi.string(buf):gsub('[^%d%.%-]', ''))
    return s == '' and '0' or s
end

local function act(code)
    if not busy then job = code end
end

local function gg(code)
    if lib.gg_run_async(code) == 0 then return nil end
    while lib.gg_busy() == 1 do wait(0) end
    return ffi.string(lib.gg_result())
end

local function parse(s)
    rows = {}
    for ad, v in s:gmatch('(%x+)|([^\n]*)') do rows[#rows + 1] = { ad = ad, v = v } end
end

local function btn(label, w, code)
    if imgui.Button(label, imgui.ImVec2(w, 38)) then act(code) end
end

imgui.OnFrame(function() return show[0] end, function()
    imgui.SetNextWindowSize(imgui.ImVec2(460, 0), imgui.Cond.FirstUseEver)
    imgui.SetNextWindowPos(imgui.ImVec2(40, 60), imgui.Cond.FirstUseEver)
    imgui.Begin('GGSamp##w', show)

    imgui.SetNextItemWidth(190)
    imgui.InputText('##v', bufVal, ffi.sizeof(bufVal))
    imgui.SameLine()
    if imgui.Button(TYPES[ti] .. '##t', imgui.ImVec2(60, 38)) then ti = ti % #TYPES + 1 end
    imgui.SameLine()
    if imgui.Button(REGS[ri] .. '##r', imgui.ImVec2(90, 38)) then ri = ri % #REGS + 1 end

    if imgui.Button('Search', imgui.ImVec2(210, 40)) then
        local v = clean(bufVal)
        if v ~= '' then
            stype = TYPES[ti]
            act("gg.ranges('" .. REGS[ri] .. "') return gg.search('" .. v .. "','" .. stype .. "')")
        end
    end
    imgui.SameLine()
    if imgui.Button('Refine', imgui.ImVec2(210, 40)) then
        local v = clean(bufVal)
        if v ~= '' then act("return gg.refine('" .. v .. "')") end
    end

    btn('Changed##c',     100, 'return gg.changed()')
    imgui.SameLine()
    btn('Unchanged##u',   100, 'return gg.unchanged()')
    imgui.SameLine()
    btn('Inc##i',         100, 'return gg.increased()')
    imgui.SameLine()
    btn('Dec##d',         100, 'return gg.decreased()')

    imgui.SetNextItemWidth(250)
    imgui.InputText('##w', bufW, ffi.sizeof(bufW))
    imgui.SameLine()
    imgui.TextColored(imgui.ImVec4(0.6, 0.6, 0.6, 1), 'nilai tulis')

    if imgui.Button('Edit all##ea', imgui.ImVec2(100, 38)) then act('return gg.editAll(' .. num(bufW) .. ')') end
    imgui.SameLine()
    if imgui.Button('Frz all##fa', imgui.ImVec2(100, 38)) then act('return gg.freezeAll(' .. num(bufW) .. ')') end
    imgui.SameLine()
    btn('Unfrz##uf', 100, 'gg.unfreezeAll()')
    imgui.SameLine()
    btn('Clear##cl', 100, 'gg.clear()')

    imgui.Text(status)
    imgui.BeginChild('##res', imgui.ImVec2(0, 260), true)
    for i, r in ipairs(rows) do
        imgui.Text('0x' .. r.ad .. ' = ' .. r.v)
        imgui.SameLine(300)
        if imgui.Button('W##w' .. i, imgui.ImVec2(50, 36)) then
            act('return gg.write(0x' .. r.ad .. ',' .. num(bufW) .. ",'" .. stype .. "')")
        end
        imgui.SameLine()
        if imgui.Button('F##f' .. i, imgui.ImVec2(50, 36)) then
            act('gg.freeze(0x' .. r.ad .. ',' .. num(bufW) .. ",'" .. stype .. "')")
        end
    end
    imgui.EndChild()
    imgui.End()
end)

function main()
    while not isSampAvailable() do wait(100) end
    wait(1500)
    if not ok then
        sampAddChatMessage('[GG] gagal load libggsamp.so', 0xFF4444)
        return
    end
    sampAddChatMessage('[GG] siap, /gg buka menu', 0x00FFCC)
    sampRegisterChatCommand('gg', function() show[0] = not show[0] end)
    while true do
        wait(0)
        if job then
            local c = job
            job, busy, status = nil, true, 'memproses...'
            local r = gg(c)
            status = r and (r:gsub('%s+$', '')) or 'sibuk'
            local l = gg(LIST)
            if l then parse(l) end
            busy = false
        end
    end
end
