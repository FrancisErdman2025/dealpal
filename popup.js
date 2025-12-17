// popup.js - DealPal (Amazon, Walmart, eBay detection + duplicate prevention + delete X)
// Full file - replace existing popup.js

document.addEventListener('DOMContentLoaded', () => {
  const scanBtn = document.getElementById('scanBtn');
  const trackedList = document.getElementById('trackedList');
  const consentCheckbox = document.getElementById('consent');
  const lastSeenDiv = document.getElementById('lastSeen');

  // Normalize stored items from various shapes
  function normalizeStoredItems(data) {
    if (!data) return [];
    if (Array.isArray(data)) return data;
    if (typeof data === 'object') {
      try {
        return Object.keys(data).map(k => data[k]);
      } catch (e) {
        return [];
      }
    }
    return [];
  }

  // Load and render
  function loadAll() {
    chrome.storage.local.get(['trackedItems', 'tracked_items', 'share_consent'], (data) => {
      let items = [];
      if (data.trackedItems) items = normalizeStoredItems(data.trackedItems);
      else if (data.tracked_items) items = normalizeStoredItems(data.tracked_items);
      else items = [];
      renderTracked(items);
      consentCheckbox.checked = !!data.share_consent;
    });
  }

  // Render list with delete buttons
  function renderTracked(items) {
    trackedList.innerHTML = '';
    if (!items || items.length === 0) {
      trackedList.innerHTML = '<div class="no-items" style="color:var(--muted)">No tracked items yet.</div>';
      return;
    }

    items.forEach(item => {
      const node = document.createElement('div');
      node.className = 'item';
      const title = escapeHtml(item.title || item.url || 'Unknown product');
      const priceDisplay = item.priceText ? escapeHtml(item.priceText) : 'Price not detected';

      node.innerHTML = `
        <div class="meta">
          <div class="title">${title}</div>
          <div class="price">${priceDisplay}</div>
          <div style="margin-top:6px"><a href="${item.url}" target="_blank" rel="noopener noreferrer">View product</a></div>
        </div>
        <div style="margin-left:8px;">
          <button class="deleteBtn" data-url="${item.url}" title="Delete">X</button>
        </div>
      `;
      trackedList.appendChild(node);
    });

    // attach delete handlers
    Array.from(trackedList.querySelectorAll('.deleteBtn')).forEach(btn => {
      btn.addEventListener('click', (e) => {
        const url = e.currentTarget.getAttribute('data-url');
        deleteTrackedByUrl(url);
      });
    });
  }

  // Save array to storage
  function saveTrackedArray(arr, cb) {
    chrome.storage.local.set({ trackedItems: arr }, () => {
      if (typeof cb === 'function') cb();
    });
  }

  // Delete by URL and clear duplicate message
  function deleteTrackedByUrl(url) {
    chrome.storage.local.get(['trackedItems', 'tracked_items'], (data) => {
      let items = [];
      if (data.trackedItems) items = normalizeStoredItems(data.trackedItems);
      else if (data.tracked_items) items = normalizeStoredItems(data.tracked_items);
      else items = [];
      const filtered = items.filter(i => i.url !== url);
      saveTrackedArray(filtered, () => {
        renderTracked(filtered);
        lastSeenDiv.textContent = '';
      });
    });
  }

  // Duplicate check by url/title
  function isDuplicate(product, items) {
    if (!items || !items.length) return false;
    return items.some(i =>
      (i.url && product.url && i.url === product.url) ||
      (i.title && product.title && i.title === product.title)
    );
  }

  // Escape HTML
  function escapeHtml(text) {
    if (!text) return '';
    return String(text).replace(/[&<>"'`]/g, s => {
      const map = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;', '`': '&#96;' };
      return map[s];
    });
  }

  // The script injected into the page to extract product info robustly for Amazon, Walmart, eBay
  async function scanActiveTab() {
    try {
      const tabs = await chrome.tabs.query({ active: true, currentWindow: true });
      if (!tabs || tabs.length === 0) {
        lastSeenDiv.textContent = 'No active tab found.';
        return;
      }
      const tab = tabs[0];

      const results = await chrome.scripting.executeScript({
        target: { tabId: tab.id },
        func: function getProductInfo() {
          // Runs in page context
          function textOf(el) { return el ? (el.innerText || el.textContent || '').trim() : ''; }
          function visible(el) {
            if (!el) return false;
            const style = window.getComputedStyle(el);
            if (style && (style.visibility === 'hidden' || style.display === 'none')) return false;
            const rect = el.getBoundingClientRect();
            return rect && rect.width > 0 && rect.height > 0;
          }
          function numericFromText(s) {
            if (!s) return null;
            const m = s.match(/\$?\s*([0-9]{1,3}(?:[,\s][0-9]{3})*(?:\.[0-9]{2})?)/);
            if (!m) return null;
            return parseFloat(m[1].replace(/[,\s]/g, ''));
          }

          // 1) Title heuristics
          const titleSelectors = [
            '#productTitle', // Amazon
            'h1.prod-ProductTitle', // walmart old
            'h1[itemprop="name"]',
            'h1', // fallback
            '[data-testid="product-title"]',
            '.product-title', '.itm-title', '#itemTitle', '.vi-quantity' // ebay-ish
          ];
          let title = '';
          for (const sel of titleSelectors) {
            const el = document.querySelector(sel);
            if (el && textOf(el).length) { title = textOf(el); break; }
          }
          if (!title) title = document.title || '';

          // 2) Hostname-specific selectors
          const host = location.hostname || '';
          let priceText = null;

          // AMAZON selectors
          if (host.includes('amazon.')) {
            const amazonSelectors = [
              '#priceblock_ourprice',
              '#priceblock_dealprice',
              '#priceblock_saleprice',
              '#price_inside_buybox',
              '.a-price .a-offscreen',
              '[data-a-color="price"] .a-offscreen'
            ];
            for (const s of amazonSelectors) {
              const el = document.querySelector(s);
              if (el && textOf(el)) { priceText = textOf(el); break; }
            }
          }

          // WALMART selectors
          if (!priceText && host.includes('walmart.')) {
            const walmartSelectors = [
              '[itemprop="price"]',
              '[data-testid="price"]',
              '.price-characteristic', // numeric pieces
              '.price-group', '.price-main .visuallyhidden', '.prod-PriceHero .price-characteristic',
              '.price .visuallyhidden'
            ];
            for (const s of walmartSelectors) {
              const el = document.querySelector(s);
              if (el && textOf(el)) { priceText = textOf(el); break; }
            }
            // meta og price
            if (!priceText) {
              const meta = document.querySelector('meta[property="og:price:amount"], meta[itemprop="price"]');
              if (meta && meta.content) priceText = meta.content;
            }
          }

          // EBAY selectors
          if (!priceText && host.includes('ebay.')) {
            const ebaySelectors = [
              '#prcIsum', '#mm-saleDscPrc', '.display-price', '.notranslate', '[itemprop="price"]', '.vi-price'
            ];
            for (const s of ebaySelectors) {
              const el = document.querySelector(s);
              if (el && textOf(el)) { priceText = textOf(el); break; }
            }
            // ebay sometimes uses meta
            if (!priceText) {
              const meta = document.querySelector('meta[itemprop="price"], meta[property="product:price:amount"]');
              if (meta && meta.content) priceText = meta.content;
            }
          }

          // 3) Generic fallback: find nearest $ element to title
          if (!priceText) {
            let candidate = null;
            const dollarRegex = /\$\s*\d/;
            const els = Array.from(document.querySelectorAll('span,div,meta,a,li,button'));
            const visibleEls = els.filter(e => visible(e) && (textOf(e) && dollarRegex.test(textOf(e))));
            if (visibleEls.length) {
              if (title) {
                // choose the one with minimal DOM distance to element containing title
                let titleEl = null;
                for (const sel of titleSelectors) {
                  const te = document.querySelector(sel);
                  if (te && textOf(te).length) { titleEl = te; break; }
                }
                if (titleEl) {
                  // compute DOM distance as path difference
                  function domPath(el) {
                    const path = [];
                    while (el && el !== document) {
                      let idx = 0;
                      let sib = el;
                      while ((sib = sib.previousElementSibling) != null) idx++;
                      path.unshift(idx);
                      el = el.parentElement;
                    }
                    return path;
                  }
                  const tPath = domPath(titleEl);
                  let best = {el:null,dist:1e9};
                  for (const e of visibleEls) {
                    const p = domPath(e);
                    // simple distance: difference in arrays
                    let dist = 0;
                    const len = Math.max(tPath.length, p.length);
                    for (let i=0;i<len;i++) {
                      const a = tPath[i]||0;
                      const b = p[i]||0;
                      dist += Math.abs(a-b);
                    }
                    if (dist < best.dist) { best = {el:e, dist}; }
                  }
                  candidate = best.el;
                } else {
                  candidate = visibleEls[0];
                }
              } else {
                candidate = visibleEls[0];
              }
            }
            if (candidate) priceText = textOf(candidate);
          }

          // 4) final parse
          const numeric = numericFromText(priceText);
          return {
            title: title || '',
            priceText: priceText || null,
            price: numeric,
            url: location.href,
            ts: Date.now()
          };
        }
      });

      if (!results || !results[0] || !results[0].result) {
        lastSeenDiv.textContent = 'No product information returned from page.';
        return;
      }
      const product = results[0].result;

      lastSeenDiv.textContent = `Scanned: ${product.title ? product.title.substring(0,60) : product.url}`;

      // existing items
      chrome.storage.local.get(['trackedItems', 'tracked_items'], (data) => {
        let items = [];
        if (data.trackedItems) items = normalizeStoredItems(data.trackedItems);
        else if (data.tracked_items) items = normalizeStoredItems(data.tracked_items);
        else items = [];

        if (isDuplicate(product, items)) {
          lastSeenDiv.textContent = 'This page is already tracked. Delete first to add again.';
          return;
        }

        items.unshift(product);
        saveTrackedArray(items, () => {
          renderTracked(items);
          lastSeenDiv.textContent = 'Added to tracked items';
        });
      });

    } catch (err) {
      console.error('scanActiveTab error', err);
      lastSeenDiv.textContent = 'Scan failed. See console.';
    }
  }

  // Wire up scan
  scanBtn.addEventListener('click', () => {
    scanActiveTab();
  });

  // Consent toggle
  consentCheckbox.addEventListener('change', () => {
    chrome.storage.local.set({ share_consent: consentCheckbox.checked });
  });

  // initialize UI
  loadAll();
});
