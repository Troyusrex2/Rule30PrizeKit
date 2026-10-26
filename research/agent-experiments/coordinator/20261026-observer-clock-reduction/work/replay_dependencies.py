from pathlib import Path
import subprocess,sys
r=Path(__file__).resolve().parent
for m in ['Rule30CommonPastResearch','Rule30ColumnReaderResearch','Rule30ReaderEquivalenceResearch',
          'Rule30ReaderCanonicalResearch','Rule30OrClockObserverResearch','Rule30ReaderObserverReductionResearch']:
    subprocess.run([sys.executable,'-B',str(r/'guard.py'),'replay.py',m],cwd=r,check=True)
