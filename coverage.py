from pathlib import Path
from pyk.kcovr import render_coverage_xml

xml = render_coverage_xml(
    definition_dirs=[Path('promela-kompiled')],
    # list the K source files you want in the report
    source_files=[Path("promela.k")],
)
Path("coverage.xml").write_text(xml)
print("Wrote coverage.xml")

