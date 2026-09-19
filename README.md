#### Automated Installation from Commit

To clone, checkout a specific commit, and perform an automated build in one command[span_7](start_span)[span_7](end_span):

```bash
git clone [https://github.com/jeffgurd888/unity-theory.git](https://github.com/jeffgurd888/unity-theory.git) && \
cd unity-theory && \
git checkout <COMMIT_HASH> && \
chmod +x install.sh && \
./install.sh
