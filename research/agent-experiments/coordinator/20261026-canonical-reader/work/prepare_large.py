from pathlib import Path
r=Path(__file__).resolve().parent
s=(r/'orbit_partition.py').read_text(encoding='utf-8')
s=s.replace('for width in range(1,25):','for width in [8,*range(25,31)]:')
s=s.replace("'orbit-partition.json'","'large-orbit-partition.json'")
s=s.replace('partition-representatives-','large-partition-representatives-')
(r/'orbit_partition_large.py').write_text(s,encoding='utf-8')
print('Prepared width8 cross-machine control and widths25..30, unchanged outer guards')
