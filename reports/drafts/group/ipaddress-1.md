<!-- title: Small inconsistencies in ipaddress found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. ipaddress: exploded of an IPv4-mapped IPv6 address or interface loses the scope id and the prefix

IPv6Address._explode_shorthand_ip_string formats an IPv4-mapped address by keeping the first 30 characters of the base method's result and appending the dotted quad. That was written for a base result of exactly 39 characters. IPv6Interface inherits the method, and its base result ends in /prefixlen, so IPv6Interface('::ffff:1.2.3.4/64').exploded is '0000:0000:0000:0000:0000:ffff:1.2.3.4', with no /64. Since gh-88178 the base result of a scoped address ends in %scope, so IPv6Address('::ffff:1.2.3.4%eth0').exploded loses its scope id too, which is the one thing that fix set out to keep. str() and compressed show both. exploded of every address and interface outside ::ffff:0:0/96 keeps them.

<details><summary>Reproducer</summary>

```python
import ipaddress
i = ipaddress.IPv6Interface('::ffff:1.2.3.4/64')
a = ipaddress.IPv6Address('::ffff:1.2.3.4%eth0')
print(i.compressed, '->', i.exploded)
print(a.compressed, '->', a.exploded)
print('round trip:', ipaddress.IPv6Interface(i.exploded), 'vs', i)
if not i.exploded.endswith('/64') and 'eth0' not in a.exploded:
    print("Observed the reported behavior.")
```

</details>

#### 2. ipaddress: IPv6Network.exploded raises AddressValueError for a network with a scope id

IPv6Network('fe80::%eth0/64') builds, and its str(), compressed and network_address work, but its exploded raises AddressValueError: "Only hex digits permitted in '%eth0' in 'fe80::%eth0'". gh-88178 fixed exactly this for IPv6Address and IPv6Interface in 3.15, by parsing a string without the scope id. The third branch of the same function was left alone: _explode_shorthand_ip_string still parses str(self.network_address), which carries the scope id, and then has code that would never reach it, since `_BaseNetwork` returns before the `if self._scope_id:` test.

<details><summary>Reproducer</summary>

```python
import ipaddress
net = ipaddress.IPv6Network('fe80::%eth0/64')
print(str(net), net.compressed, net.network_address.scope_id)
try:
    print(net.exploded)
except ipaddress.AddressValueError as e:
    print('AddressValueError:', e)
    print("Observed the reported behavior.")
```

</details>

#### 3. ipaddress: whether IPv4Network(('10.0.0.0', 8.0)) works depends on earlier calls; otherwise it leaks AttributeError

_make_netmask looks up `arg in cls._netmask_cache` before it checks `isinstance(arg, int)`. The cache is keyed by value, so 8.0, Decimal(8) and True find the entries stored for the ints 8 and 1. In a fresh interpreter IPv4Network(('10.0.0.0', 8.0)) reaches _prefix_from_prefix_string, which calls 8.0.isascii() and leaks AttributeError: 'float' object has no attribute 'isascii'. After any call that cached the int 8 (e.g. IPv4Network('10.0.0.0/8') or IPv4Network(('10.0.0.0', 8))), the same call succeeds and returns 10.0.0.0/8. So the same expression raises or succeeds depending on what ran before, and the failure is an internal AttributeError rather than the documented NetmaskValueError/TypeError. The same missing type check lets bytes masks through: IPv4Network(('10.0.0.0', b'8')) is accepted as /8, while IPv4Network(('10.0.0.0', b'255.0.0.0')) leaks "TypeError: a bytes-like object is required, not 'str'" from _prefix_from_ip_string's str operations, and so does ipaddress.ip_network(('10.0.0.0', b'255.0.0.0')), whose fallback catches only ValueError subclasses. (Found by the second ipaddress review; checked on 3.15.2 and main.)

<details><summary>Reproducer</summary>

```python
import subprocess, sys
prog = (
    "import ipaddress\n"
    "def t(cls, a, m):\n"
    "    try: return str(cls((a, m)))\n"
    "    except Exception as e: return type(e).__name__\n"
    "r4 = t(ipaddress.IPv4Network, '10.0.0.0', 8.0)\n"
    "r6 = t(ipaddress.IPv6Network, '2001:db8::', 64.0)\n"
    "ipaddress.IPv4Network(('10.0.0.0', 8)); ipaddress.IPv6Network(('2001:db8::', 64))\n"
    "print(r4, t(ipaddress.IPv4Network, '10.0.0.0', 8.0), r6, t(ipaddress.IPv6Network, '2001:db8::', 64.0))\n")
out = subprocess.run([sys.executable, '-c', prog], capture_output=True, text=True).stdout.split()
print(out)
if out == ['AttributeError', '10.0.0.0/8', 'AttributeError', '2001:db8::/64']:
    print("Observed the reported behavior.")
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
AI tools (Claude and Codex) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
