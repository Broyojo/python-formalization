import json, subprocess
qs = ["zoneinfo datetime subclass", "zoneinfo subclass fold", "zoneinfo toordinal", "zoneinfo subclass utcoffset",
      "zoneinfo fromutc footer", "zoneinfo fromutc tz_after", "zoneinfo fromutc static", "zoneinfo fromutc utcoffset inconsistent",
      "zoneinfo subclass cache", "zoneinfo strong cache subclass", "zoneinfo __init_subclass__", "zoneinfo get_local_timestamp"]
for q in qs:
    out = subprocess.run(["gh", "search", "issues", "--repo", "python/cpython", *q.split(),
                          "--limit", "10", "--json", "number,title,state"], capture_output=True, text=True)
    print("==", q)
    try:
        for i in json.loads(out.stdout):
            print(" ", i["number"], i["state"], i["title"])
    except Exception:
        print(" ERR", out.stderr[:200])
