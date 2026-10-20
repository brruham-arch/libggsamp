#include <pthread.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <cstdint>
#include <cctype>
#include <algorithm>
#include <string>
#include <vector>
#include <mutex>
#include <atomic>
#include <thread>
extern "C" {
#include "lua.h"
#include "lualib.h"
#include "lauxlib.h"
}

enum { I8, I16, I32, I64, F32, F64, NT };
struct TInfo { const char* name; int size; bool fp; };
static const TInfo TI[NT] = {{"i8",1,false},{"i16",2,false},{"i32",4,false},{"i64",8,false},{"f32",4,true},{"f64",8,true}};

static lua_State* L = nullptr;
static std::mutex G, FM, RM, WM;
static std::string outbuf, initMsg, spec = "anon";

struct Hit { uint64_t addr, old; };
static Hit* H = nullptr;
static size_t HN = 0;
static int curType = I32;
static const size_t MAXHITS = 2000000;
static const size_t CHUNK = 1 << 20;
static const size_t PIPE_CH = 32768;
static int rp[2] = {-1, -1}, wp[2] = {-1, -1};

static int getType(lua_State* s, int idx) {
    const char* n = luaL_optstring(s, idx, "i32");
    for (int i = 0; i < NT; i++) if (!strcmp(n, TI[i].name)) return i;
    luaL_error(s, "tipe tidak dikenal: %s (i8 i16 i32 i64 f32 f64)", n);
    return 0;
}

static void pushVal(lua_State* s, int t, uint64_t raw) {
    switch (t) {
        case I8: lua_pushinteger(s, (int8_t)raw); break;
        case I16: lua_pushinteger(s, (int16_t)raw); break;
        case I32: lua_pushinteger(s, (int32_t)raw); break;
        case I64: lua_pushinteger(s, (int64_t)raw); break;
        case F32: { float f; memcpy(&f, &raw, 4); lua_pushnumber(s, f); break; }
        default: { double d; memcpy(&d, &raw, 8); lua_pushnumber(s, d); }
    }
}

static uint64_t toRaw(lua_State* s, int idx, int t) {
    uint64_t r = 0;
    switch (t) {
        case I8: { int8_t v = (int8_t)luaL_checkinteger(s, idx); memcpy(&r, &v, 1); break; }
        case I16: { int16_t v = (int16_t)luaL_checkinteger(s, idx); memcpy(&r, &v, 2); break; }
        case I32: { int32_t v = (int32_t)luaL_checkinteger(s, idx); memcpy(&r, &v, 4); break; }
        case I64: { int64_t v = (int64_t)luaL_checkinteger(s, idx); memcpy(&r, &v, 8); break; }
        case F32: { float v = (float)luaL_checknumber(s, idx); memcpy(&r, &v, 4); break; }
        default: { double v = luaL_checknumber(s, idx); memcpy(&r, &v, 8); }
    }
    return r;
}

template <typename T> static int c3(T a, T b) { return a < b ? -1 : (a > b ? 1 : 0); }
static int cmpRaw(int t, uint64_t a, uint64_t b) {
    switch (t) {
        case I8: { int8_t x, y; memcpy(&x, &a, 1); memcpy(&y, &b, 1); return c3(x, y); }
        case I16: { int16_t x, y; memcpy(&x, &a, 2); memcpy(&y, &b, 2); return c3(x, y); }
        case I32: { int32_t x, y; memcpy(&x, &a, 4); memcpy(&y, &b, 4); return c3(x, y); }
        case I64: { int64_t x, y; memcpy(&x, &a, 8); memcpy(&y, &b, 8); return c3(x, y); }
        case F32: { float x, y; memcpy(&x, &a, 4); memcpy(&y, &b, 4); return c3(x, y); }
        default: { double x, y; memcpy(&x, &a, 8); memcpy(&y, &b, 8); return c3(x, y); }
    }
}

struct Cond { int t; double lo, hi; int64_t ilo, ihi; };

static void parseCond(lua_State* s, int idx, int t, Cond& c) {
    c.t = t;
    double dlo = 0, dhi = 0;
    int64_t ilo = 0, ihi = 0;
    if (lua_type(s, idx) == LUA_TSTRING) {
        std::string v = lua_tostring(s, idx);
        size_t p = v.find('~');
        std::string a = (p == std::string::npos) ? v : v.substr(0, p);
        std::string b = (p == std::string::npos) ? v : v.substr(p + 1);
        dlo = strtod(a.c_str(), nullptr); dhi = strtod(b.c_str(), nullptr);
        ilo = strtoll(a.c_str(), nullptr, 10); ihi = strtoll(b.c_str(), nullptr, 10);
    } else if (lua_isinteger(s, idx)) {
        ilo = ihi = lua_tointeger(s, idx);
        dlo = dhi = (double)ilo;
    } else {
        dlo = dhi = luaL_checknumber(s, idx);
        ilo = ihi = (int64_t)dlo;
    }
    if (t == F32 && dlo == dhi) dlo = dhi = (double)(float)dlo;
    c.lo = dlo; c.hi = dhi; c.ilo = ilo; c.ihi = ihi;
}

static inline bool matchRaw(const Cond& c, const uint8_t* p) {
    switch (c.t) {
        case I8: { int8_t v; memcpy(&v, p, 1); return v >= c.ilo && v <= c.ihi; }
        case I16: { int16_t v; memcpy(&v, p, 2); return v >= c.ilo && v <= c.ihi; }
        case I32: { int32_t v; memcpy(&v, p, 4); return v >= c.ilo && v <= c.ihi; }
        case I64: { int64_t v; memcpy(&v, p, 8); return v >= c.ilo && v <= c.ihi; }
        case F32: { float v; memcpy(&v, p, 4); return (double)v >= c.lo && (double)v <= c.hi; }
        default: { double v; memcpy(&v, p, 8); return v >= c.lo && v <= c.hi; }
    }
}

struct Region { uint64_t s, e; std::string perms, path; };

static std::vector<Region> readMaps() {
    std::vector<Region> v;
    FILE* f = fopen("/proc/self/maps", "r");
    if (!f) return v;
    char line[1024];
    while (fgets(line, sizeof line, f)) {
        unsigned long long a, b;
        char perms[8];
        int off = 0;
        if (sscanf(line, "%llx-%llx %7s %*s %*s %*s %n", &a, &b, perms, &off) < 3) continue;
        std::string path = off > 0 ? std::string(line + off) : std::string();
        while (!path.empty() && (path.back() == '\n' || path.back() == ' ')) path.pop_back();
        v.push_back({(uint64_t)a, (uint64_t)b, perms, path});
    }
    fclose(f);
    return v;
}

enum { C_CA, C_CH, C_CB, C_CD, C_CS, C_A, C_J, C_O, NC };
static const char* CN[NC] = {"ca", "ch", "cb", "cd", "cs", "a", "j", "o"};
static inline unsigned bit(int c) { return 1u << c; }
static unsigned gmask = 0;
static std::vector<std::string> gsubs;

static int classify(const Region& r) {
    const std::string& p = r.path;
    if (p.empty()) return C_A;
    auto has = [&](const char* x) { return p.find(x) != std::string::npos; };
    if (p == "[heap]") return C_CH;
    if (p.compare(0, 6, "[stack") == 0) return C_CS;
    if (p[0] == '[') {
        if (has("scudo") || has("libc_malloc") || has("jemalloc")) return C_CA;
        if (has(".bss")) return C_CB;
        if (has("dalvik")) return C_J;
        return C_A;
    }
    if (has("dalvik") || (p.size() > 4 && p.compare(p.size() - 4, 4, ".art") == 0)) return C_J;
    if (has(".so")) return C_CD;
    return C_O;
}

static void setSpec(const std::string& v) {
    gmask = 0;
    gsubs.clear();
    size_t i = 0;
    while (i <= v.size()) {
        size_t j = v.find_first_of("+,; ", i);
        if (j == std::string::npos) j = v.size();
        std::string tk = v.substr(i, j - i);
        i = j + 1;
        if (tk.empty()) continue;
        std::string lc = tk;
        for (auto& ch : lc) ch = (char)tolower((unsigned char)ch);
        if (lc == "all") { gmask = (1u << NC) - 1; continue; }
        if (lc == "anon") { gmask |= bit(C_A) | bit(C_CA) | bit(C_CH) | bit(C_CB) | bit(C_CS) | bit(C_J); continue; }
        if (lc == "native") { gmask |= bit(C_A) | bit(C_CA) | bit(C_CH) | bit(C_CB) | bit(C_CS); continue; }
        bool code = false;
        for (int k = 0; k < NC; k++) if (lc == CN[k]) { gmask |= bit(k); code = true; break; }
        if (!code) gsubs.push_back(tk);
    }
}

static bool rwBase(const Region& r) {
    if (r.perms[0] != 'r' || r.perms[1] != 'w') return false;
    const std::string& p = r.path;
    if (p.find("/dev/") != std::string::npos) return false;
    if (p.compare(0, 5, "[vvar") == 0 || p.compare(0, 5, "[vdso") == 0) return false;
    return true;
}

static bool wanted(const Region& r) {
    if (!rwBase(r)) return false;
    int c = classify(r);
    if (gmask & bit(c)) return true;
    if (c == C_CD || c == C_O) {
        for (auto& sub : gsubs) if (r.path.find(sub) != std::string::npos) return true;
    }
    return false;
}

static void drain(int fd) { char t[4096]; while (read(fd, t, sizeof t) > 0) {} }

static size_t memRead(uint64_t addr, void* dst, size_t len) {
    std::lock_guard<std::mutex> g(RM);
    if (rp[0] < 0) return 0;
    uint8_t* d = (uint8_t*)dst;
    size_t done = 0;
    while (done < len) {
        size_t n = std::min(PIPE_CH, len - done);
        ssize_t w = write(rp[1], (const void*)(uintptr_t)(addr + done), n);
        if (w <= 0) break;
        size_t got = 0;
        while (got < (size_t)w) {
            ssize_t r = read(rp[0], d + done + got, (size_t)w - got);
            if (r <= 0) break;
            got += (size_t)r;
        }
        if (got < (size_t)w) drain(rp[0]);
        done += got;
        if (got < n) break;
    }
    return done;
}

static bool memWriteFast(uint64_t addr, const void* src, size_t len) {
    if (len == 0 || len > PIPE_CH) return false;
    std::lock_guard<std::mutex> g(WM);
    if (wp[0] < 0) return false;
    if (write(wp[1], src, len) != (ssize_t)len) { drain(wp[0]); return false; }
    ssize_t r = read(wp[0], (void*)(uintptr_t)addr, len);
    if (r == (ssize_t)len) return true;
    drain(wp[0]);
    return false;
}

static bool memWriteForce(uint64_t addr, const void* src, size_t len) {
    for (auto& r : readMaps()) {
        if (addr >= r.s && addr + len <= r.e) {
            if (r.perms[0] != 'r') return false;
            uint64_t ps = (uint64_t)sysconf(_SC_PAGESIZE);
            uint64_t pa = addr & ~(ps - 1);
            uint64_t pe = (addr + len + ps - 1) & ~(ps - 1);
            int orig = PROT_READ | (r.perms[1] == 'w' ? PROT_WRITE : 0) | (r.perms[2] == 'x' ? PROT_EXEC : 0);
            if (mprotect((void*)(uintptr_t)pa, (size_t)(pe - pa), orig | PROT_WRITE) != 0) return false;
            memcpy((void*)(uintptr_t)addr, src, len);
            mprotect((void*)(uintptr_t)pa, (size_t)(pe - pa), orig);
            if (r.perms[2] == 'x') __builtin___clear_cache((char*)(uintptr_t)addr, (char*)(uintptr_t)(addr + len));
            return true;
        }
    }
    return false;
}

static bool memWrite(uint64_t addr, const void* src, size_t len) {
    return memWriteFast(addr, src, len) || memWriteForce(addr, src, len);
}

static bool readRaw(uint64_t a, int t, uint64_t& raw) {
    raw = 0;
    return memRead(a, &raw, (size_t)TI[t].size) == (size_t)TI[t].size;
}

static std::string probeText() {
    static volatile int32_t tv = 0x12345678;
    int32_t got = 0;
    uint64_t addr = (uint64_t)(uintptr_t)&tv;
    bool rd = memRead(addr, &got, 4) == 4 && got == 0x12345678;
    int32_t nv = 0x0badf00d;
    bool wr = memWrite(addr, &nv, 4) && tv == 0x0badf00d;
    tv = 0x12345678;
    return std::string("io: baca ") + (rd ? "ok" : "GAGAL") + ", tulis " + (wr ? "ok" : "GAGAL") + "\n";
}

static int l_print(lua_State* s) {
    int n = lua_gettop(s);
    for (int i = 1; i <= n; i++) {
        size_t len;
        const char* p = luaL_tolstring(s, i, &len);
        if (i > 1) outbuf += '\t';
        outbuf.append(p, len);
        lua_pop(s, 1);
    }
    outbuf += '\n';
    return 0;
}

static int l_ranges(lua_State* s) {
    std::string v = luaL_optstring(s, 1, spec.c_str());
    spec = v;
    setSpec(v);
    size_t n = 0, bytes = 0;
    for (auto& r : readMaps()) if (wanted(r)) { n++; bytes += (size_t)(r.e - r.s); }
    lua_pushinteger(s, (lua_Integer)n);
    lua_pushnumber(s, bytes / 1048576.0);
    return 2;
}

static int l_regions(lua_State*) {
    size_t cnt[NC] = {0};
    double mb[NC] = {0};
    for (auto& r : readMaps()) {
        if (!rwBase(r)) continue;
        int c = classify(r);
        cnt[c]++;
        mb[c] += (r.e - r.s) / 1048576.0;
    }
    char b[96];
    for (int i = 0; i < NC; i++) {
        snprintf(b, sizeof b, "%-3s %5zu region %9.1f MB\n", CN[i], cnt[i], mb[i]);
        outbuf += b;
    }
    outbuf += "aktif: " + spec + "\n";
    return 0;
}

static int l_probe(lua_State*) { outbuf += probeText(); return 0; }

static int l_maps(lua_State* s) {
    const char* f = luaL_optstring(s, 1, "");
    lua_newtable(s);
    int i = 1;
    for (auto& r : readMaps()) {
        if (*f && r.path.find(f) == std::string::npos) continue;
        char b[1200];
        snprintf(b, sizeof b, "%llx-%llx %s %s", (unsigned long long)r.s, (unsigned long long)r.e, r.perms.c_str(), r.path.c_str());
        lua_pushstring(s, b);
        lua_rawseti(s, -2, i++);
    }
    return 1;
}

static int l_base(lua_State* s) {
    const char* name = luaL_checkstring(s, 1);
    for (auto& r : readMaps()) {
        if (r.path.find(name) != std::string::npos) { lua_pushinteger(s, (lua_Integer)r.s); return 1; }
    }
    lua_pushnil(s);
    return 1;
}

static int l_search(lua_State* s) {
    int t = getType(s, 2);
    Cond c;
    parseCond(s, 1, t, c);
    if (!H) return luaL_error(s, "array hasil gagal dialokasikan");
    HN = 0;
    curType = t;
    int sz = TI[t].size;
    bool trunc = false;
    size_t rdOK = 0, rdFail = 0;
    std::vector<uint8_t> buf(CHUNK);
    uint64_t b0 = (uint64_t)(uintptr_t)buf.data(), b1 = b0 + buf.size();
    uint64_t hb = (uint64_t)(uintptr_t)H, he = hb + (uint64_t)MAXHITS * sizeof(Hit);
    for (auto& r : readMaps()) {
        if (!wanted(r)) continue;
        uint64_t a = (r.s + sz - 1) / sz * sz;
        while (a + sz <= r.e && !trunc) {
            if (a >= hb && a < he) { a = he; continue; }
            uint64_t lim = r.e;
            if (a < hb && hb < lim) lim = hb;
            size_t want = (size_t)std::min<uint64_t>(CHUNK, lim - a);
            want -= want % sz;
            if (!want) break;
            size_t n = memRead(a, buf.data(), want);
            size_t adv;
            if (n >= (size_t)sz) {
                rdOK += n;
                size_t usable = n - (n % sz);
                for (size_t o = 0; o < usable; o += sz) {
                    if (!matchRaw(c, &buf[o])) continue;
                    uint64_t ad = a + o;
                    if (ad >= b0 && ad < b1) continue;
                    if (HN >= MAXHITS) { trunc = true; break; }
                    Hit h; h.addr = ad; h.old = 0;
                    memcpy(&h.old, &buf[o], sz);
                    H[HN++] = h;
                }
                adv = usable;
            } else {
                rdFail += want;
                adv = std::min<size_t>(want, 4096);
            }
            a += adv;
        }
        if (trunc) break;
    }
    if (trunc) outbuf += "[peringatan] hasil dipotong di batas 2000000, persempit nilai/ranges\n";
    if (rdFail) {
        char b[160];
        snprintf(b, sizeof b, "[info] dibaca %.1f MB, gagal baca %.1f MB\n", rdOK / 1048576.0, rdFail / 1048576.0);
        outbuf += b;
    }
    lua_pushinteger(s, (lua_Integer)HN);
    return 1;
}

static int doRefine(lua_State* s, int mode, const Cond* c) {
    int t = curType;
    size_t k = 0;
    for (size_t i = 0; i < HN; i++) {
        Hit h = H[i];
        uint64_t cur = 0;
        if (!readRaw(h.addr, t, cur)) continue;
        bool keep = false;
        switch (mode) {
            case 0: keep = matchRaw(*c, (const uint8_t*)&cur); break;
            case 1: keep = cur != h.old; break;
            case 2: keep = cur == h.old; break;
            case 3: keep = cmpRaw(t, cur, h.old) > 0; break;
            case 4: keep = cmpRaw(t, cur, h.old) < 0; break;
        }
        if (keep) { h.old = cur; H[k++] = h; }
    }
    HN = k;
    lua_pushinteger(s, (lua_Integer)k);
    return 1;
}

static int l_refine(lua_State* s) { Cond c; parseCond(s, 1, curType, c); return doRefine(s, 0, &c); }
static int l_changed(lua_State* s) { return doRefine(s, 1, nullptr); }
static int l_unchanged(lua_State* s) { return doRefine(s, 2, nullptr); }
static int l_increased(lua_State* s) { return doRefine(s, 3, nullptr); }
static int l_decreased(lua_State* s) { return doRefine(s, 4, nullptr); }
static int l_count(lua_State* s) { lua_pushinteger(s, (lua_Integer)HN); return 1; }
static int l_clear(lua_State*) {
    HN = 0;
    if (H) madvise(H, (size_t)MAXHITS * sizeof(Hit), MADV_DONTNEED);
    return 0;
}

static int l_results(lua_State* s) {
    size_t n = (size_t)luaL_optinteger(s, 1, 20);
    size_t off = (size_t)luaL_optinteger(s, 2, 0);
    lua_newtable(s);
    int idx = 1;
    for (size_t i = off; i < HN && i < off + n; i++) {
        uint64_t cur;
        lua_newtable(s);
        lua_pushinteger(s, (lua_Integer)H[i].addr);
        lua_setfield(s, -2, "addr");
        if (readRaw(H[i].addr, curType, cur)) pushVal(s, curType, cur); else lua_pushnil(s);
        lua_setfield(s, -2, "value");
        lua_rawseti(s, -2, idx++);
    }
    return 1;
}

static int l_read(lua_State* s) {
    uint64_t a = (uint64_t)luaL_checkinteger(s, 1);
    int t = getType(s, 2);
    uint64_t raw;
    if (!readRaw(a, t, raw)) { lua_pushnil(s); return 1; }
    pushVal(s, t, raw);
    return 1;
}

static int l_write(lua_State* s) {
    uint64_t a = (uint64_t)luaL_checkinteger(s, 1);
    int t = getType(s, 3);
    uint64_t raw = toRaw(s, 2, t);
    lua_pushboolean(s, memWrite(a, &raw, (size_t)TI[t].size));
    return 1;
}

static int l_editAll(lua_State* s) {
    uint64_t raw = toRaw(s, 1, curType);
    size_t ok = 0;
    for (size_t i = 0; i < HN; i++)
        if (memWriteFast(H[i].addr, &raw, (size_t)TI[curType].size)) { H[i].old = raw; ok++; }
    lua_pushinteger(s, (lua_Integer)ok);
    return 1;
}

struct Fz { uint64_t addr; int t; uint64_t raw; };
static std::vector<Fz> fz;
static bool fzStarted = false;

static void* freezer(void*) {
    for (;;) {
        usleep(30000);
        std::lock_guard<std::mutex> g(FM);
        for (auto& f : fz) memWriteFast(f.addr, &f.raw, (size_t)TI[f.t].size);
    }
    return nullptr;
}

static void addFreeze(uint64_t a, int t, uint64_t raw) {
    std::lock_guard<std::mutex> g(FM);
    for (auto& f : fz) if (f.addr == a) { f.t = t; f.raw = raw; return; }
    fz.push_back({a, t, raw});
    if (!fzStarted) {
        fzStarted = true;
        pthread_t th;
        pthread_create(&th, nullptr, freezer, nullptr);
        pthread_detach(th);
    }
}

static int l_freeze(lua_State* s) {
    uint64_t a = (uint64_t)luaL_checkinteger(s, 1);
    int t = getType(s, 3);
    addFreeze(a, t, toRaw(s, 2, t));
    return 0;
}

static int l_freezeAll(lua_State* s) {
    uint64_t raw = toRaw(s, 1, curType);
    for (size_t i = 0; i < HN; i++) addFreeze(H[i].addr, curType, raw);
    lua_pushinteger(s, (lua_Integer)HN);
    return 1;
}

static int l_unfreeze(lua_State* s) {
    uint64_t a = (uint64_t)luaL_checkinteger(s, 1);
    std::lock_guard<std::mutex> g(FM);
    for (size_t i = 0; i < fz.size(); i++) if (fz[i].addr == a) { fz.erase(fz.begin() + i); break; }
    return 0;
}

static int l_unfreezeAll(lua_State*) { std::lock_guard<std::mutex> g(FM); fz.clear(); return 0; }
static int l_frozen(lua_State* s) { std::lock_guard<std::mutex> g(FM); lua_pushinteger(s, (lua_Integer)fz.size()); return 1; }

static const char* PRELUDE = R"LUA(
function gg.show(n, off)
  off = off or 0
  local r = gg.results(n or 20, off)
  for i, h in ipairs(r) do
    print(string.format("%d. 0x%x = %s", i + off, h.addr, tostring(h.value)))
  end
  print("total: " .. gg.count())
end
function gg.load(name) return dofile(gg.dir .. "/" .. name) end
function gg.hex(n) return string.format("0x%x", n) end
)LUA";

static void doInit(const std::string& dir) {
    if (L) return;
    if (pipe2(rp, O_NONBLOCK | O_CLOEXEC) != 0) rp[0] = rp[1] = -1;
    if (pipe2(wp, O_NONBLOCK | O_CLOEXEC) != 0) wp[0] = wp[1] = -1;
    void* m = mmap(nullptr, (size_t)MAXHITS * sizeof(Hit), PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    H = (m == MAP_FAILED) ? nullptr : (Hit*)m;
    setSpec(spec);
    L = luaL_newstate();
    luaL_openlibs(L);
    lua_pushcfunction(L, l_print);
    lua_setglobal(L, "print");
    static const luaL_Reg fns[] = {
        {"ranges", l_ranges}, {"regions", l_regions}, {"probe", l_probe},
        {"maps", l_maps}, {"base", l_base},
        {"search", l_search}, {"refine", l_refine},
        {"changed", l_changed}, {"unchanged", l_unchanged},
        {"increased", l_increased}, {"decreased", l_decreased},
        {"count", l_count}, {"clear", l_clear}, {"results", l_results},
        {"read", l_read}, {"write", l_write}, {"editAll", l_editAll},
        {"freeze", l_freeze}, {"freezeAll", l_freezeAll},
        {"unfreeze", l_unfreeze}, {"unfreezeAll", l_unfreezeAll}, {"frozen", l_frozen},
        {nullptr, nullptr}};
    luaL_newlib(L, fns);
    lua_pushstring(L, dir.c_str());
    lua_setfield(L, -2, "dir");
    lua_setglobal(L, "gg");
    std::string pp = "package.path=package.path..';" + dir + "/?.lua'";
    luaL_dostring(L, pp.c_str());
    luaL_dostring(L, PRELUDE);
    lua_settop(L, 0);
    initMsg = probeText();
    std::string a = dir + "/autoexec.lua";
    if (access(a.c_str(), R_OK) == 0) {
        outbuf.clear();
        if (luaL_dofile(L, a.c_str())) {
            initMsg += std::string("autoexec error: ") + lua_tostring(L, -1) + "\n";
        } else initMsg += outbuf;
        lua_settop(L, 0);
    }
}

static std::string runLua(const std::string& code) {
    std::lock_guard<std::mutex> g(G);
    if (!L) return "belum init\n";
    outbuf = initMsg;
    initMsg.clear();
    int top = lua_gettop(L);
    std::string ex = "return " + code;
    int st = luaL_loadstring(L, ex.c_str());
    if (st != LUA_OK) { lua_settop(L, top); st = luaL_loadstring(L, code.c_str()); }
    if (st == LUA_OK) st = lua_pcall(L, 0, LUA_MULTRET, 0);
    if (st != LUA_OK) {
        const char* m = lua_tostring(L, -1);
        outbuf += "error: ";
        outbuf += m ? m : "?";
        outbuf += '\n';
    } else {
        int n = lua_gettop(L) - top;
        if (n > 0) {
            for (int i = 1; i <= n; i++) {
                size_t len;
                const char* p = luaL_tolstring(L, top + i, &len);
                if (i > 1) outbuf += '\t';
                outbuf.append(p, len);
                lua_pop(L, 1);
            }
            outbuf += '\n';
        }
    }
    lua_settop(L, top);
    return outbuf;
}

/* ---------- API C untuk ffi.load (MoNetLoader) ---------- */
#define EXP extern "C" __attribute__((visibility("default")))

static std::atomic<bool> busyF{false};
static std::string cres;
static std::mutex CM;

EXP int gg_init(const char* dir) {
    std::lock_guard<std::mutex> g(G);
    doInit(std::string(dir));
    return L != nullptr;
}

EXP int gg_run_async(const char* code) {
    if (busyF.exchange(true)) return 0;
    std::string c = code;
    std::thread([c] {
        std::string r = runLua(c);
        for (auto& ch : r) if ((unsigned char)ch >= 0x80) ch = '?';
        { std::lock_guard<std::mutex> g(CM); cres = r; }
        busyF = false;
    }).detach();
    return 1;
}

EXP int gg_busy() { return busyF ? 1 : 0; }

EXP const char* gg_result() {
    static std::string out;
    std::lock_guard<std::mutex> g(CM);
    out = cres;
    return out.c_str();
}
